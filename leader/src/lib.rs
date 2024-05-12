pub mod cli;
pub mod mpt;
mod padding_and_withdrawals;
mod rpc;
pub mod utils;

use std::collections::{BTreeMap, HashMap};

use alloy::{
    consensus::TxType,
    primitives::{Address, Bloom, Bytes, FixedBytes, TxHash, B256, U256},
    providers::{ext::DebugApi as _, Provider as _},
    rpc::types::{
        eth::{EIP1186StorageProof as StorageProof, Transaction},
        trace::geth::{
            AccountState, DiffMode, GethDebugBuiltInTracerType, GethDebugTracerType,
            GethDebugTracingOptions, GethTrace, PreStateFrame, PreStateMode,
        },
    },
};
use anyhow::anyhow;
use evm_arithmetization::{
    generation::{GenerationInputs, TrieInputs},
    proof::{BlockMetadata, ExtraBlockData, TrieRoots},
};
use itertools::izip;
use mpt_trie::{
    nibbles::Nibbles,
    partial_trie::{HashedPartialTrie, Node, PartialTrie},
};
use trace_decoder::types::HashedAccountAddr;

use crate::{
    mpt::{apply_diffs, insert_mpt, trim, Mpt},
    padding_and_withdrawals::{
        add_withdrawals_to_txns, pad_gen_inputs_with_dummy_inputs_if_needed, BlockMetaAndHashes,
    },
    rpc::{get_block_hashes, CliqueGetSignersAtHashResponse, EthChainIdResponse},
    utils::{has_storage_deletion, keccak},
};

type Provider = alloy::providers::RootProvider<alloy::transports::http::Http<reqwest::Client>>;

/// Keccak of empty bytes.
pub const EMPTY_HASH: B256 = FixedBytes([
    197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202,
    130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112,
]);

/// 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421
const EMPTY_TRIE_HASH: B256 = FixedBytes([
    86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153,
    108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
]);

/// The current state of all tries as we process txn deltas. These are mutated
/// after every txn we process in the trace.
#[derive(Clone, Debug, Default)]
struct PartialTrieState {
    state: HashedPartialTrie,
    storage: HashMap<HashedAccountAddr, HashedPartialTrie>,
    txn: HashedPartialTrie,
    receipt: HashedPartialTrie,
}

/// Get the proof for an account + storage locations at a given block number.
pub async fn get_proof(
    address: Address,
    locations: Vec<B256>,
    block_number: u64,
    provider: &Provider,
) -> anyhow::Result<(Vec<Bytes>, Vec<StorageProof>, B256, bool)> {
    // tracing::info!("Proof {:?}: {:?} {:?}", block_number, address, locations);
    // println!("Proof {:?}: {:?} {:?}", block_number, address, locations);
    let proof = provider.get_proof(address, locations, block_number.into());
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
        tracer: Some(GethDebugTracerType::BuiltInTracer(
            GethDebugBuiltInTracerType::PreStateTracer,
        )),
        ..Default::default()
    }
}

fn tracing_options_diff() -> GethDebugTracingOptions {
    GethDebugTracingOptions {
        tracer: Some(GethDebugTracerType::BuiltInTracer(
            GethDebugBuiltInTracerType::PreStateTracer,
        )),
        ..GethDebugTracingOptions::default()
    }
}

/// Hash map from code hash to code.
/// Add the empty code hash to the map.
fn contract_codes() -> HashMap<B256, Vec<u8>> {
    let mut map = HashMap::new();
    map.insert(EMPTY_HASH, vec![]);
    map
}

const BLOCK_WITH_FULL_TRANSACTIONS: bool = true;

/// Get the Plonky2 block metadata at the given block number.
pub async fn get_block_metadata(
    block_number: u64,
    block_chain_id: U256,
    provider: &Provider,
    request_miner_from_clique: bool,
) -> anyhow::Result<(BlockMetadata, B256)> {
    let block = provider
        .get_block(block_number.into(), BLOCK_WITH_FULL_TRANSACTIONS)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number))?;

    let block_beneficiary = match request_miner_from_clique {
        false => block.header.miner,
        true => {
            CliqueGetSignersAtHashResponse::fetch(
                provider.client().transport().url(),
                block.header.hash.unwrap(),
            )
            .await?
            .result
            .signer
        }
    };

    Ok((
        BlockMetadata {
            block_beneficiary: crate::utils::compat::address(block_beneficiary),
            block_timestamp: block.header.timestamp.into(),
            block_number: block_number.into(),
            block_difficulty: crate::utils::compat::u256(block.header.difficulty),
            block_gaslimit: block.header.gas_limit.into(),
            block_chain_id: crate::utils::compat::u256(block_chain_id),
            block_base_fee: block.header.base_fee_per_gas.unwrap().into(),
            block_bloom: crate::utils::compat::bloom(block.header.logs_bloom),
            block_gas_used: block.header.gas_used.into(),
            block_random: crate::utils::compat::h256(block.header.mix_hash.unwrap()),
        },
        block.header.state_root,
    ))
}

pub async fn gather_witness(
    tx: TxHash,
    provider: &Provider,
    request_miner_from_clique: bool,
) -> anyhow::Result<Vec<GenerationInputs>> {
    let tx = provider.get_transaction_by_hash(tx).await?;
    let block_number = tx.block_number.unwrap();
    let tx_index = usize::try_from(tx.transaction_index.unwrap()).unwrap();

    let block = provider
        .get_block(block_number.into(), BLOCK_WITH_FULL_TRANSACTIONS)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number))?;

    let mut state_mpt = Mpt::new();
    let mut contract_codes = contract_codes();
    let mut storage_mpts: HashMap<_, Mpt> = HashMap::new();
    let mut txn_rlps = vec![];

    let chain_id = EthChainIdResponse::fetch(provider.client().transport().url())
        .await?
        .result;

    let mut alladdrs = vec![];
    let mut state = BTreeMap::<Address, AccountState>::new();
    let mut traces: Vec<BTreeMap<Address, AccountState>> = vec![];
    let mut txns_info = vec![];

    for &hash in block.transactions.hashes().take(tx_index + 1) {
        let txn = provider.get_transaction_by_hash(hash).await?;
        // chain_id = txn.chain_id.unwrap(); // TODO: For type-0 txn, the chain_id is
        // not set so the unwrap panics.
        let trace = provider
            .debug_trace_transaction(hash, tracing_options())
            .await?;
        let GethTrace::PreStateTracer(PreStateFrame::Default(PreStateMode(accounts))) = trace
        else {
            panic!();
        };
        traces.push(accounts.clone());
        for (address, account) in accounts {
            alladdrs.push(address);
            // If this account already exists, merge the storage.
            if let Some(acc) = state.get(&address) {
                let mut acc = acc.clone();
                let mut new_store = acc.storage.clone();
                let stor = account.storage;
                for (k, v) in stor {
                    new_store.insert(k, v);
                }
                acc.storage = new_store;
                state.insert(address, acc);
            } else {
                state.insert(address, account);
            }
        }
        txn_rlps.push(rlp::transaction(&txn));
        txns_info.push(txn);
    }

    for (address, account) in &state {
        let AccountState { code, storage, .. } = account;
        let empty_storage = storage.is_empty();
        let mut storage_keys = vec![];
        storage_keys.extend(storage.keys().copied());
        let (proof, storage_proof, storage_hash, _account_is_empty) =
            get_proof(*address, storage_keys.clone(), block_number - 1, provider).await?;
        insert_mpt(&mut state_mpt, proof);

        let (next_proof, next_storage_proof, _next_storage_hash, _next_account_is_empty) =
            get_proof(*address, storage_keys, block_number, provider).await?;
        insert_mpt(&mut state_mpt, next_proof);

        let key = keccak(address.0);
        if !empty_storage {
            let mut storage_mpt = Mpt::new();
            storage_mpt.root = storage_hash;
            for sp in storage_proof {
                insert_mpt(&mut storage_mpt, sp.proof);
            }
            for sp in next_storage_proof {
                insert_mpt(&mut storage_mpt, sp.proof);
            }
            storage_mpts.insert(key, storage_mpt);
        }
        if let Some(code) = code {
            let code = hex::decode(&code[2..])?;
            let codehash = keccak(&code);
            contract_codes.insert(codehash, code);
        }
    }

    for &hash in block.transactions.hashes().take(tx_index + 1) {
        let trace = provider
            .debug_trace_transaction(hash, tracing_options_diff())
            .await?;
        let GethTrace::PreStateTracer(PreStateFrame::Diff(DiffMode { post, pre })) = trace else {
            panic!()
        };

        for d in [pre, post] {
            for (address, account) in d {
                let AccountState { storage, .. } = account;
                let empty_storage = storage.is_empty();
                let mut storage_keys = vec![];
                storage_keys.extend(storage.keys().copied());

                let (proof, storage_proof, _storage_hash, _account_is_empty) =
                    get_proof(address, storage_keys.clone(), block_number - 1, provider).await?;
                insert_mpt(&mut state_mpt, proof);

                let (next_proof, next_storage_proof, _next_storage_hash, _next_account_is_empty) =
                    get_proof(address, storage_keys, block_number, provider).await?;
                insert_mpt(&mut state_mpt, next_proof);

                let key = keccak(address.0);
                if !empty_storage {
                    let mut storage_mpt = Mpt::new();
                    let storage_mpt = storage_mpts.get_mut(&key).unwrap_or(&mut storage_mpt);
                    for sp in storage_proof {
                        insert_mpt(storage_mpt, sp.proof);
                    }
                    for sp in next_storage_proof {
                        insert_mpt(storage_mpt, sp.proof);
                    }
                    // storage_mpts.insert(key.into(), storage_mpt);
                }
            }
        }
    }

    if let Some(v) = &block.withdrawals {
        for w in v {
            let (proof, _storage_proof, _storage_hash, _account_is_empty) =
                get_proof(w.address, vec![], block_number - 1, provider).await?;
            insert_mpt(&mut state_mpt, proof);
        }
    }

    let prev_block = provider
        .get_block((block_number - 1).into(), BLOCK_WITH_FULL_TRANSACTIONS)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number - 1))?;
    state_mpt.root = prev_block.header.state_root;

    let (block_metadata, _final_hash) =
        get_block_metadata(block_number, chain_id, provider, request_miner_from_clique).await?;

    let mut state_mpt = state_mpt.to_partial_trie();
    let mut txns_mpt = HashedPartialTrie::from(Node::Empty);
    let mut receipts_mpt = HashedPartialTrie::from(Node::Empty);
    let mut gas_used = U256::default();
    let mut bloom = Bloom::default();

    // Withdrawals
    let wds = block
        .withdrawals
        .map(|it| {
            it.iter()
                .map(|w| (w.address, U256::from(w.amount * 1_000_000_000))) // Alchemy returns Gweis for some reason
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();

    // Block hashes
    let block_hashes = get_block_hashes(block_number, provider.client().transport().url()).await?;

    let mut storage_mpts: HashMap<_, _> = storage_mpts
        .iter()
        .map(|(a, m)| (*a, m.to_partial_trie()))
        .collect();

    let mut proof_gen_ir = Vec::new();
    for (i, (tx, mut touched, signed_txn)) in izip!(txns_info, traces, txn_rlps)
        .enumerate()
        .take(tx_index + 1)
    {
        tracing::info!("Processing {}-th transaction: {:?}", i, tx.hash);
        let last_tx = i == block.transactions.len() - 1;
        let trace = provider
            .debug_trace_transaction(tx.hash, tracing_options_diff())
            .await?;
        let has_storage_deletion = has_storage_deletion(&trace);
        let (next_state_mpt, next_storage_mpts) = apply_diffs(
            state_mpt.clone(),
            storage_mpts.clone(),
            &mut contract_codes,
            trace,
        );
        // For the last tx, we want to include the withdrawal addresses in the state
        // trie.
        if last_tx {
            for (addr, _) in &wds {
                if !touched.contains_key(addr) {
                    touched.insert(*addr, AccountState::default());
                }
            }
        }
        let (trimmed_state_mpt, trimmed_storage_mpts) = trim(
            state_mpt.clone(),
            storage_mpts.clone(),
            touched.clone(),
            has_storage_deletion,
        );
        assert_eq!(trimmed_state_mpt.hash(), state_mpt.hash());
        let receipt = provider.get_transaction_receipt(tx.hash).await?.unwrap();
        let mut new_bloom = bloom;
        new_bloom.accrue_bloom(receipt.inner.logs_bloom());
        let mut new_txns_mpt = txns_mpt.clone();
        new_txns_mpt
            .insert(
                Nibbles::from_bytes_be(&rlp::option_u64(&receipt.transaction_index)).unwrap(),
                signed_txn.clone(),
            )
            .unwrap();
        let mut new_receipts_mpt = receipts_mpt.clone();
        let mut bytes = rlp::transaction_receipt(&receipt);
        if !matches!(receipt.transaction_type(), TxType::Legacy) {
            bytes.insert(0, receipt.transaction_type() as u8);
        }
        new_receipts_mpt
            .insert(
                Nibbles::from_bytes_be(&rlp::option_u64(&receipt.transaction_index)).unwrap(),
                bytes,
            )
            .unwrap();

        // Use withdrawals for the last tx in the block.
        let _withdrawals = if last_tx { wds.clone() } else { vec![] };
        // For the last tx, we check that the final trie roots match those in the block
        // header.

        let trie_roots_after = if last_tx {
            TrieRoots {
                state_root: crate::utils::compat::h256(block.header.state_root),
                transactions_root: crate::utils::compat::h256(block.header.transactions_root),
                receipts_root: crate::utils::compat::h256(block.header.receipts_root),
            }
        } else {
            TrieRoots {
                state_root: next_state_mpt.hash(),
                transactions_root: new_txns_mpt.hash(),
                receipts_root: new_receipts_mpt.hash(),
            }
        };
        let inputs = GenerationInputs {
            signed_txn: Some(signed_txn),
            tries: TrieInputs {
                state_trie: trimmed_state_mpt,
                transactions_trie: txns_mpt.clone(),
                receipts_trie: receipts_mpt.clone(),
                storage_tries: trimmed_storage_mpts
                    .into_iter()
                    .map(|(k, v)| (crate::utils::compat::h256(k), v))
                    .collect(),
            },
            withdrawals: vec![],
            contract_code: contract_codes
                .clone()
                .into_iter()
                .map(|(k, v)| (crate::utils::compat::h256(k), v))
                .collect(),
            block_metadata: block_metadata.clone(),
            block_hashes: block_hashes.clone(),
            gas_used_before: crate::utils::compat::u256(gas_used),
            gas_used_after: crate::utils::compat::u256(gas_used + U256::from(receipt.gas_used)),
            checkpoint_state_trie_root: crate::utils::compat::h256(prev_block.header.state_root), /* TODO: make it configurable */
            trie_roots_after,
            txn_number_before: receipt.transaction_index.unwrap().into(), /* TODO(aatifsyed): is
                                                                           * this unwrap ok? */
        };

        state_mpt = next_state_mpt;
        storage_mpts = next_storage_mpts;
        gas_used += U256::from(receipt.gas_used);
        assert_eq!(gas_used, U256::from(receipt.inner.cumulative_gas_used()));
        bloom = new_bloom;
        txns_mpt = new_txns_mpt;
        receipts_mpt = new_receipts_mpt;

        proof_gen_ir.push(inputs);
    }

    let b_data = BlockMetaAndHashes {
        b_meta: block_metadata,
        b_hashes: block_hashes,
    };

    let initial_tries_for_dummies = proof_gen_ir
        .first()
        .map(|ir| PartialTrieState {
            state: ir.tries.state_trie.clone(),
            txn: ir.tries.transactions_trie.clone(),
            receipt: ir.tries.receipts_trie.clone(),
            storage: HashMap::from_iter(ir.tries.storage_tries.iter().cloned()),
        })
        .unwrap_or_else(|| {
            // No starting tries to work with, so we will have tries that are 100% hashed
            // out.
            PartialTrieState {
                state: create_fully_hashed_out_trie_from_hash(block.header.state_root),
                txn: create_fully_hashed_out_trie_from_hash(EMPTY_TRIE_HASH),
                receipt: create_fully_hashed_out_trie_from_hash(EMPTY_TRIE_HASH),
                storage: HashMap::default(),
            }
        });

    let initial_extra_data = ExtraBlockData {
        checkpoint_state_trie_root: crate::utils::compat::h256(prev_block.header.state_root),
        ..Default::default()
    };

    let mut final_tries = PartialTrieState {
        state: state_mpt,
        storage: storage_mpts
            .into_iter()
            .map(|(k, v)| (crate::utils::compat::h256(k), v))
            .collect(),
        txn: txns_mpt,
        receipt: receipts_mpt,
    };

    let final_extra_data = proof_gen_ir
        .last()
        .map(|ir| ExtraBlockData {
            checkpoint_state_trie_root: crate::utils::compat::h256(prev_block.header.state_root),
            txn_number_before: ir.txn_number_before,
            txn_number_after: ir.txn_number_before,
            gas_used_before: ir.gas_used_after,
            gas_used_after: ir.gas_used_after,
        })
        .unwrap_or_else(|| initial_extra_data.clone());

    pad_gen_inputs_with_dummy_inputs_if_needed(
        &mut proof_gen_ir,
        &b_data,
        &final_extra_data,
        &initial_extra_data,
        &initial_tries_for_dummies,
        &final_tries,
        !wds.is_empty(),
    );

    add_withdrawals_to_txns(&mut proof_gen_ir, &mut final_tries, wds);

    Ok(proof_gen_ir)
}

fn create_fully_hashed_out_trie_from_hash(h: B256) -> HashedPartialTrie {
    let h = crate::utils::compat::h256(h);
    let mut trie = HashedPartialTrie::default();
    trie.insert(Nibbles::default(), h).unwrap();

    trie
}

pub mod rlp {
    use alloy::rpc::types::eth::TransactionReceipt;

    use super::*;

    pub fn transaction(_: &Transaction) -> Vec<u8> {
        todo!()
    }
    pub fn transaction_receipt(_: &TransactionReceipt) -> Vec<u8> {
        todo!()
    }
    pub fn option_u64(it: &Option<u64>) -> Vec<u8> {
        let mut v = vec![];
        alloy::rlp::encode_list(it.as_slice(), &mut v);
        v
    }
}
