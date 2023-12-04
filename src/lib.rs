#![allow(clippy::needless_range_loop)]

pub mod utils;

use itertools::izip;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use anyhow::{anyhow, Result};
use eth_trie_utils::nibbles::Nibbles;
use eth_trie_utils::partial_trie::{HashedPartialTrie, Node, PartialTrie};
use eth_trie_utils::trie_subsets::create_trie_subset;
use ethers::prelude::*;
use ethers::types::GethDebugTracerType;
use ethers::utils::keccak256;
use ethers::utils::rlp;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::plonk::config::KeccakGoldilocksConfig;
use plonky2::util::timing::TimingTree;
use plonky2_evm::all_stark::AllStark;
use plonky2_evm::config::StarkConfig;
use plonky2_evm::generation::mpt::AccountRlp;
use plonky2_evm::generation::{GenerationInputs, TrieInputs};
use plonky2_evm::proof::BlockMetadata;
use plonky2_evm::proof::{BlockHashes, TrieRoots};
use plonky2_evm::prover::prove_with_outputs;

#[derive(Clone, Debug)]
pub struct MptNode(Vec<u8>);

#[derive(Default)]
pub struct Mpt {
    pub mpt: HashMap<H256, MptNode>,
    pub root: H256,
}

impl Mpt {
    pub fn new() -> Self {
        Self {
            mpt: HashMap::new(),
            root: H256::zero(),
        }
    }

    pub fn to_partial_trie(&self) -> HashedPartialTrie {
        self.to_partial_trie_helper(self.root)
    }
    fn to_partial_trie_helper(&self, root: H256) -> HashedPartialTrie {
        let node = self.mpt.get(&root);
        let data = if let Some(mpt_node) = node {
            mpt_node.0.clone()
        } else {
            return Node::Hash(root).into();
        };
        let a = rlp::decode_list::<Vec<u8>>(&data);
        match a.len() {
            17 => {
                let value = a[16].clone();
                let mut children = vec![];
                for i in 0..16 {
                    if a[i].is_empty() {
                        children.push(Node::Empty.into());
                        continue;
                    }
                    children.push(
                        Arc::new(Box::new(self.to_partial_trie_helper(H256::from_slice(&a[i]))))
                    );
                }
                Node::Branch {
                    value,
                    children: children.try_into().unwrap(),
                }
                .into()
            }
            2 => match a[0][0] >> 4 {
                0 => {
                    let ext_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
                    Node::Extension {
                        nibbles: ext_prefix,
                        child: Arc::new(
                            Box::new(self.to_partial_trie_helper(H256::from_slice(&a[1])))
                        ),
                    }
                    .into()
                }
                1 => {
                    let b = a[0][0] & 0xf;
                    let mut ext_prefix = if a[0].len() > 1 {
                        Nibbles::from_bytes_be(&a[0][1..]).unwrap()
                    } else {
                        Nibbles {
                            count: 0,
                            packed: U512::zero(),
                        }
                    };
                    ext_prefix.push_nibble_front(b);
                    Node::Extension {
                        nibbles: ext_prefix,
                        child: Arc::new(
                            Box::new(self.to_partial_trie_helper(H256::from_slice(&a[1])))
                        ),
                    }
                    .into()
                }
                2 => {
                    let leaf_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
                    Node::Leaf {
                        nibbles: leaf_prefix,
                        value: a[1].clone(),
                    }
                    .into()
                }
                3 => {
                    let b = a[0][0] & 0xf;
                    let mut leaf_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
                    leaf_prefix.push_nibble_front(b);
                    Node::Leaf {
                        nibbles: leaf_prefix,
                        value: a[1].clone(),
                    }
                    .into()
                }
                _ => panic!("wtf?"),
            },
            _ => panic!("wtf?"),
        }
    }
}

pub fn insert_mpt(mpt: &mut Mpt, proof: Vec<Bytes>) {
    for p in proof.into_iter() {
        mpt.mpt.insert(H256(keccak256(&p)), MptNode(p.to_vec()));
    }
}

pub fn apply_diffs(
    mut mpt: HashedPartialTrie,
    mut storage: HashMap<H256, HashedPartialTrie>,
    contract_code: &mut HashMap<H256, Vec<u8>>,
    trace: GethTrace,
) -> (HashedPartialTrie, HashMap<H256, HashedPartialTrie>) {
    let diff = if let GethTrace::Known(GethTraceFrame::PreStateTracer(PreStateFrame::Diff(diff))) =
        trace
    {
        diff
    } else {
        panic!("wtf?");
    };

    let empty_node = HashedPartialTrie::from(Node::Empty);

    let tokk = |k: H256| Nibbles::from_bytes_be(&keccak256(k.0)).unwrap();

    for (addr, old) in &diff.pre {
        let key = H256(keccak256(addr.0));
        if !diff.post.contains_key(addr) {
            storage.remove(&key);
        } else {
            let new = diff.post.get(addr).unwrap();
            if old.storage.clone().unwrap_or_default().is_empty()
                && new.storage.clone().unwrap_or_default().is_empty()
            {
                continue;
            }
            let mut trie = storage.get(&key).unwrap().clone();
            for (&k, &v) in &old.storage.clone().unwrap_or_default() {
                if !new.storage.clone().unwrap_or_default().contains_key(&k) {
                    trie.delete(tokk(k));
                } else {
                    let sanity = trie.get(tokk(k)).unwrap();
                    let sanity = rlp::decode::<U256>(sanity).unwrap();
                    assert_eq!(sanity, v.into_uint());
                    let w = *new.storage.clone().unwrap_or_default().get(&k).unwrap();
                    trie.insert(tokk(k), rlp::encode(&w.into_uint()).to_vec());
                }
            }
            for (&k, v) in &new.storage.clone().unwrap_or_default() {
                if !old.storage.clone().unwrap_or_default().contains_key(&k) {
                    trie.insert(tokk(k), rlp::encode(&v.into_uint()).to_vec());
                }
            }
            storage.insert(key, trie);
        }
    }

    for (addr, new) in &diff.post {
        let key = H256(keccak256(addr.0));
        if !diff.pre.contains_key(addr) {
            let mut trie = HashedPartialTrie::from(Node::Empty);
            for (&k, v) in &new.storage.clone().unwrap_or_default() {
                trie.insert(tokk(k), rlp::encode(v).to_vec());
            }
            storage.insert(key, trie);
        }
    }

    dbg!("Storage done");

    let tok = |addr: &Address| Nibbles::from_bytes_be(&keccak256(addr.0)).unwrap();

    // Delete accounts that are not in the post state.
    for addr in diff.pre.keys() {
        if !diff.post.contains_key(addr) {
            dbg!("q1");
            mpt.delete(tok(addr));
        }
    }

    for (addr, acc) in &diff.post {
        if !diff.pre.contains_key(addr) {
            // New account
            let code_hash = acc
                .code
                .clone()
                .map(|s| {
                    if s.is_empty() {
                        EMPTY_HASH
                    } else {
                        let code = s.split_at(2).1;
                        let bytes = hex::decode(code).unwrap();
                        let h = H256(keccak256(&bytes));
                        contract_code.insert(h, bytes);
                        h
                    }
                })
                .unwrap_or(EMPTY_HASH);
            let account = AccountRlp {
                nonce: acc.nonce.unwrap_or(U256::zero()),
                balance: acc.balance.unwrap_or(U256::zero()),
                storage_root: storage
                    .get(&H256(keccak256(addr.0)))
                    .unwrap_or(&empty_node.clone())
                    .hash(),
                code_hash,
            };
            mpt.insert(tok(addr), rlp::encode(&account).to_vec());
        } else {
            let old = mpt
                .get(tok(addr))
                .map(|d| rlp::decode(d).unwrap())
                .unwrap_or(AccountRlp {
                    nonce: U256::zero(),
                    balance: U256::zero(),
                    storage_root: empty_node.hash(),
                    code_hash: EMPTY_HASH,
                });
            let code_hash = acc
                .code
                .clone()
                .map(|s| {
                    if s.is_empty() {
                        EMPTY_HASH
                    } else {
                        let code = s.split_at(2).1;
                        let bytes = hex::decode(code).unwrap();
                        let h = H256(keccak256(&bytes));
                        contract_code.insert(h, bytes);
                        h
                    }
                })
                .unwrap_or(old.code_hash);
            let account = AccountRlp {
                nonce: acc.nonce.unwrap_or(old.nonce),
                balance: acc.balance.unwrap_or(old.balance),
                storage_root: storage
                    .get(&H256(keccak256(addr.0)))
                    .map(|trie| trie.hash())
                    .unwrap_or(old.storage_root),
                code_hash,
            };
            mpt.insert(tok(addr), rlp::encode(&account).to_vec());
        }
    }

    (mpt, storage)
}

fn trim(
    trie: HashedPartialTrie,
    mut storage_mpts: HashMap<H256, HashedPartialTrie>,
    touched: BTreeMap<Address, AccountState>,
) -> (HashedPartialTrie, HashMap<H256, HashedPartialTrie>) {
    let tok = |addr: &Address| Nibbles::from_bytes_be(&keccak256(addr.0)).unwrap();
    let keys = touched.keys().map(tok).collect::<Vec<_>>();
    let new_state_trie = create_trie_subset(&trie, keys).unwrap();
    let keys_to_addrs = touched
        .keys()
        .map(|addr| (H256(keccak256(addr.0)), *addr))
        .collect::<HashMap<_, _>>();
    for (k, t) in storage_mpts.iter_mut() {
        if !keys_to_addrs.contains_key(k) {
            *t = HashedPartialTrie::from(Node::Hash(t.hash()));
        } else {
            let addr = keys_to_addrs.get(k).unwrap();
            let acc = touched.get(addr).unwrap();
            let keys = acc
                .storage
                .clone()
                .unwrap_or_default()
                .keys()
                .map(|slot| Nibbles::from_bytes_be(&keccak256(slot.0)).unwrap())
                .collect::<Vec<_>>();
            *t = create_trie_subset(t, keys).unwrap();
        }
    }
    (new_state_trie, storage_mpts)
}

/// Keccak of empty bytes.
const EMPTY_HASH: H256 = H256([
    197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202,
    130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112,
]);

/// Get the proof for an account + storage locations at a given block number.
pub async fn get_proof(
    address: Address,
    locations: Vec<H256>,
    block_number: U64,
    provider: &Provider<Http>,
) -> Result<(Vec<Bytes>, Vec<StorageProof>, H256, bool)> {
    let proof = provider.get_proof(address, locations, Some(block_number.into()));
    let proof = proof.await?;
    let is_empty =
        proof.balance.is_zero() && proof.nonce.is_zero() && proof.code_hash == EMPTY_HASH;
    Ok((
        proof.account_proof,
        proof.storage_proof,
        proof.storage_hash,
        is_empty,
    ))
}

/// Tracing options for the debug_traceTransaction call.
fn tracing_options() -> GethDebugTracingOptions {
    GethDebugTracingOptions {
        tracer: Some(GethDebugTracerType::BuiltInTracer(GethDebugBuiltInTracerType::PreStateTracer)),

        ..GethDebugTracingOptions::default()
    }
}

fn tracing_options_diff() -> GethDebugTracingOptions {
    GethDebugTracingOptions {
        tracer: Some(GethDebugTracerType::BuiltInTracer(GethDebugBuiltInTracerType::PreStateTracer)),

        tracer_config: Some(GethDebugTracerConfig::BuiltInTracer(
            GethDebugBuiltInTracerConfig::PreStateTracer(PreStateConfig {
                diff_mode: Some(true),
            }),
        )),
        ..GethDebugTracingOptions::default()
    }
}

/// Hash map from code hash to code.
/// Add the empty code hash to the map.
fn contract_codes() -> HashMap<H256, Vec<u8>> {
    let mut map = HashMap::new();
    map.insert(EMPTY_HASH, vec![]);
    map
}

fn convert_bloom(bloom: Bloom) -> [U256; 8] {
    let mut other_bloom = [U256::zero(); 8];
    for i in 0..8 {
        other_bloom[i] = U256::from_big_endian(&bloom.0[i * 32..(i + 1) * 32]);
    }
    other_bloom
}

/// Get the Plonky2 block metadata at the given block number.
pub async fn get_block_metadata(
    block_number: U64,
    block_chain_id: U256,
    provider: &Provider<Http>,
) -> Result<(BlockMetadata, H256)> {
    let block = provider
        .get_block(block_number)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number))?;
    Ok((
        BlockMetadata {
            block_beneficiary: block.author.unwrap(),
            block_timestamp: block.timestamp,
            block_number: U256([block_number.0[0], 0, 0, 0]),
            block_difficulty: block.difficulty,
            block_gaslimit: block.gas_limit,
            block_chain_id,
            block_base_fee: block.base_fee_per_gas.unwrap(),
            block_bloom: convert_bloom(block.logs_bloom.unwrap()),
            block_gas_used: block.gas_used,
            block_random: H256::zero(), // TODO
        },
        block.state_root,
    ))
}

/// Prove an Ethereum block given its block number and some extra storage slots.
pub async fn gather_witness_and_prove_tx(tx: Transaction, provider: &Provider<Http>) -> Result<()> {
    let block_number = tx.block_number.unwrap().0[0];
    let tx_index = tx.transaction_index.unwrap().0[0] as usize;
    let block = provider
        .get_block(block_number)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number))?;
    let mut state_mpt = Mpt::new();
    let mut contract_codes = contract_codes();
    let mut storage_mpts = vec![];
    let mut txn_rlps = vec![];
    let chain_id = U256::one();
    let mut alladdrs = vec![];
    let mut state = BTreeMap::<Address, AccountState>::new();
    let mut traces: Vec<BTreeMap<Address, AccountState>> = vec![];
    let mut txns_info = vec![];
    for &hash in block.transactions.iter().take(tx_index + 1) {
        let txn = provider.get_transaction(hash);
        let txn = txn
            .await?
            .ok_or_else(|| anyhow!("Transaction not found."))?;
        // chain_id = txn.chain_id.unwrap(); // TODO: For type-0 txn, the chain_id is not set so the unwrap panics.
        let trace = provider
            .debug_trace_transaction(hash, tracing_options())
            .await?;
        let accounts = if let GethTrace::Known(
            GethTraceFrame::PreStateTracer(PreStateFrame::Default(accounts))
        ) = trace
        {
            accounts.0
        } else {
            panic!("wtf?");
        };
        traces.push(accounts.clone());
        for (address, account) in accounts {
            alladdrs.push(address);
            // If this account already exists, merge the storage.
            if let Some(acc) = state.get(&address) {
                let mut acc = acc.clone();
                let mut new_store = acc.storage.clone().unwrap_or_default();
                let stor = account.storage;
                if let Some(s) = stor {
                    for (k, v) in s {
                        new_store.insert(k, v);
                    }
                }
                acc.storage = if new_store.is_empty() {
                    None
                } else {
                    Some(new_store)
                };
                state.insert(address, acc);
            } else {
                state.insert(address, account);
            }
        }
        txn_rlps.push(txn.rlp().to_vec());
        txns_info.push(txn);
    }

    for (address, account) in &state {
        let AccountState { code, storage, .. } = account;
        let empty_storage = storage.is_none();
        let mut storage_keys = vec![];
        if let Some(stor) = storage {
            storage_keys.extend(stor.keys().copied());
        }
        let (proof, storage_proof, storage_hash, _account_is_empty) =
            get_proof(*address, storage_keys, (block_number - 1).into(), provider).await?;
        let key = keccak256(address.0);
        insert_mpt(&mut state_mpt, proof);
        if !empty_storage {
            let mut storage_mpt = Mpt::new();
            storage_mpt.root = storage_hash;
            for sp in storage_proof {
                insert_mpt(&mut storage_mpt, sp.proof);
            }
            storage_mpts.push((key.into(), storage_mpt));
        }
        if let Some(code) = code {
            let code = hex::decode(&code[2..])?;
            let codehash = keccak256(&code);
            contract_codes.insert(codehash.into(), code);
        }
    }

    let prev_block = provider
        .get_block(block_number - 1)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number - 1))?;
    state_mpt.root = prev_block.state_root;

    let (block_metadata, _final_hash) =
        get_block_metadata(block_number.into(), chain_id, provider).await?;

    prove_tx(
        tx_index,
        txn_rlps,
        block_metadata,
        state_mpt,
        contract_codes,
        storage_mpts
            .iter()
            .map(|(a, m)| (*a, m.to_partial_trie()))
            .collect(),
        txns_info,
        traces,
        provider,
    )
    .await
}

/// Actually prove the block using Plonky2.
/// If the block fails because of some unknown storage location, return the storage location.
async fn prove_tx(
    tx_index: usize,
    signed_txns: Vec<Vec<u8>>,
    block_metadata: BlockMetadata,
    state_mpt: Mpt,
    mut contract_code: HashMap<H256, Vec<u8>>,
    mut storage_mpts: HashMap<H256, HashedPartialTrie>,
    txns_info: Vec<Transaction>,
    traces: Vec<BTreeMap<Address, AccountState>>,
    provider: &Provider<Http>,
) -> Result<()> {
    let mut state_mpt = state_mpt.to_partial_trie();
    let mut txns_mpt = HashedPartialTrie::from(Node::Empty);
    let mut receipts_mpt = HashedPartialTrie::from(Node::Empty);
    let mut gas_used = U256::zero();
    let mut bloom: Bloom = Bloom::zero();
    for (i, (tx, touched, signed_txn)) in izip!(txns_info, traces, signed_txns)
        .enumerate()
        .take(tx_index + 1)
    {
        log::info!("Processing {}-th transaction: {:?}", i, tx.hash);
        println!("Processing {}-th transaction: {:?}", i, tx.hash);
        let trace = provider
            .debug_trace_transaction(tx.hash, tracing_options_diff())
            .await?;
        let (next_state_mpt, next_storage_mpts) = apply_diffs(
            state_mpt.clone(),
            storage_mpts.clone(),
            &mut contract_code,
            trace,
        );
        let (trimmed_state_mpt, trimmed_storage_mpts) =
            trim(state_mpt.clone(), storage_mpts.clone(), touched);
        let receipt = provider.get_transaction_receipt(tx.hash).await?.unwrap();
        let mut new_bloom = bloom;
        new_bloom.accrue_bloom(&receipt.logs_bloom);
        let mut new_txns_mpt = txns_mpt.clone();
        new_txns_mpt.insert(
            Nibbles::from_bytes_be(&rlp::encode(&receipt.transaction_index)).unwrap(),
            signed_txn.clone(),
        );
        let mut new_receipts_mpt = receipts_mpt.clone();
        let mut bytes = rlp::encode(&receipt).to_vec();
        if !receipt.transaction_type.unwrap().is_zero() {
            bytes.insert(0, receipt.transaction_type.unwrap().0[0] as u8);
        }
        new_receipts_mpt.insert(
            Nibbles::from_bytes_be(&rlp::encode(&receipt.transaction_index)).unwrap(),
            bytes,
        );
        let inputs = GenerationInputs {
            signed_txn: Some(signed_txn),
            tries: TrieInputs {
                state_trie: trimmed_state_mpt,
                transactions_trie: txns_mpt.clone(),
                receipts_trie: receipts_mpt.clone(),
                storage_tries: trimmed_storage_mpts.into_iter().collect(),
            },
            withdrawals: vec![],
            contract_code: contract_code.clone(),
            block_metadata: block_metadata.clone(),
            addresses: vec![],
            block_bloom_before: convert_bloom(bloom),
            block_bloom_after: convert_bloom(new_bloom),
            block_hashes: BlockHashes {
                prev_hashes: vec![H256::zero(); 256], // TODO
                cur_hash: H256::zero(),               // TODO
            },
            gas_used_before: gas_used,
            gas_used_after: gas_used + receipt.gas_used.unwrap(),
            genesis_state_trie_root: H256::zero(),
            trie_roots_after: TrieRoots {
                state_root: next_state_mpt.hash(),
                transactions_root: new_txns_mpt.hash(),
                receipts_root: new_receipts_mpt.hash(),
            },
            txn_number_before: receipt.transaction_index.0[0].into(),
        };
        if i == tx_index {
            log::info!("Proving {}-th transaction: {:?}", i, tx.hash);
            println!("Proving {}-th transaction: {:?}", i, tx.hash);
            let _proof = prove_with_outputs::<GoldilocksField, KeccakGoldilocksConfig, 2>(
                &AllStark::default(),
                &StarkConfig::standard_fast_config(),
                inputs,
                &mut TimingTree::default(),
            )?;
        }
        println!("Success");
        state_mpt = next_state_mpt;
        storage_mpts = next_storage_mpts;
        gas_used += receipt.gas_used.unwrap();
        assert_eq!(gas_used, receipt.cumulative_gas_used);
        bloom = new_bloom;
        txns_mpt = new_txns_mpt;
        receipts_mpt = new_receipts_mpt;
    }

    Ok(())
}
