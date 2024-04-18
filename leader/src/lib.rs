#![allow(clippy::needless_range_loop)]

pub mod cli;
pub mod mpt;
mod rpc;
pub mod utils;

mod padding_and_withdrawals;

use std::collections::{BTreeMap, HashMap};

use anyhow::{anyhow, Result};
use ethers::prelude::*;
use ethers::types::GethDebugTracerType;
use ethers::utils::rlp;
use evm_arithmetization::generation::{GenerationInputs, TrieInputs};
use evm_arithmetization::proof::TrieRoots;
use evm_arithmetization::proof::{BlockMetadata, ExtraBlockData};
use itertools::izip;
use mpt_trie::nibbles::Nibbles;
use mpt_trie::partial_trie::{HashedPartialTrie, Node, PartialTrie};
use padding_and_withdrawals::{
    add_withdrawals_to_txns, pad_gen_inputs_with_dummy_inputs_if_needed, BlockMetaAndHashes,
};
use rpc::{CliqueGetSignersAtHashResponse, EthChainIdResponse};
use trace_decoder::types::{HashedAccountAddr, TrieRootHash};

use crate::utils::{has_storage_deletion, keccak};
use crate::{
    mpt::{apply_diffs, insert_mpt, trim, Mpt},
    rpc::get_block_hashes,
};

/// Keccak of empty bytes.
pub const EMPTY_HASH: H256 = H256([
    197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202,
    130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112,
]);

/// 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421
const EMPTY_TRIE_HASH: H256 = H256([
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
    locations: Vec<H256>,
    block_number: U64,
    provider: &Provider<Http>,
) -> Result<(Vec<Bytes>, Vec<StorageProof>, H256, bool)> {
    // tracing::info!("Proof {:?}: {:?} {:?}", block_number, address, locations);
    // println!("Proof {:?}: {:?} {:?}", block_number, address, locations);
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
        tracer: Some(GethDebugTracerType::BuiltInTracer(
            GethDebugBuiltInTracerType::PreStateTracer,
        )),

        ..GethDebugTracingOptions::default()
    }
}

fn tracing_options_diff() -> GethDebugTracingOptions {
    GethDebugTracingOptions {
        tracer: Some(GethDebugTracerType::BuiltInTracer(
            GethDebugBuiltInTracerType::PreStateTracer,
        )),

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
    request_miner_from_clique: bool,
) -> Result<(BlockMetadata, H256)> {
    let block = provider
        .get_block(block_number)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number))?;

    let block_beneficiary = match request_miner_from_clique {
        false => block.author.unwrap(),
        true => {
            CliqueGetSignersAtHashResponse::fetch(provider.url().to_string(), block.hash.unwrap())
                .await?
                .result
                .signer
        }
    };

    Ok((
        BlockMetadata {
            block_beneficiary,
            block_timestamp: block.timestamp,
            block_number: U256([block_number.0[0], 0, 0, 0]),
            block_difficulty: block.difficulty,
            block_gaslimit: block.gas_limit,
            block_chain_id,
            block_base_fee: block.base_fee_per_gas.unwrap(),
            block_bloom: convert_bloom(block.logs_bloom.unwrap()),
            block_gas_used: block.gas_used,
            block_random: block.mix_hash.unwrap(),
        },
        block.state_root,
    ))
}

pub async fn gather_witness(
    tx: TxHash,
    provider: &Provider<Http>,
    request_miner_from_clique: bool,
) -> Result<Vec<GenerationInputs>> {
    let tx = provider
        .get_transaction(tx)
        .await?
        .ok_or_else(|| anyhow!("Transaction not found."))?;
    let block_number = tx.block_number.unwrap().0[0];
    let tx_index = tx.transaction_index.unwrap().0[0] as usize;

    let block = provider
        .get_block(block_number)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number))?;

    let mut state_mpt = Mpt::new();
    let mut contract_codes = contract_codes();
    let mut storage_mpts: HashMap<_, Mpt> = HashMap::new();
    let mut txn_rlps = vec![];

    let chain_id = EthChainIdResponse::fetch(provider.url().to_string())
        .await?
        .result;

    let mut alladdrs = vec![];
    let mut state = BTreeMap::<Address, AccountState>::new();
    let mut traces: Vec<BTreeMap<Address, AccountState>> = vec![];
    let mut txns_info = vec![];

    for &hash in block.transactions.iter().take(tx_index + 1) {
        let txn = provider.get_transaction(hash);
        let txn = txn
            .await?
            .ok_or_else(|| anyhow!("Transaction not found."))?;
        // chain_id = txn.chain_id.unwrap(); // TODO: For type-0 txn, the chain_id is
        // not set so the unwrap panics.
        let trace = provider
            .debug_trace_transaction(hash, tracing_options())
            .await?;
        let accounts = if let GethTrace::Known(GethTraceFrame::PreStateTracer(
            PreStateFrame::Default(accounts),
        )) = trace
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
        let (proof, storage_proof, storage_hash, _account_is_empty) = get_proof(
            *address,
            storage_keys.clone(),
            (block_number - 1).into(),
            provider,
        )
        .await?;
        insert_mpt(&mut state_mpt, proof);

        let (next_proof, next_storage_proof, _next_storage_hash, _next_account_is_empty) =
            get_proof(*address, storage_keys, block_number.into(), provider).await?;
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
            storage_mpts.insert(key.into(), storage_mpt);
        }
        if let Some(code) = code {
            let code = hex::decode(&code[2..])?;
            let codehash = keccak(&code);
            contract_codes.insert(codehash.into(), code);
        }
    }

    for &hash in block.transactions.iter().take(tx_index + 1) {
        let trace = provider
            .debug_trace_transaction(hash, tracing_options_diff())
            .await?;
        let diff =
            if let GethTrace::Known(GethTraceFrame::PreStateTracer(PreStateFrame::Diff(diff))) =
                trace
            {
                diff
            } else {
                panic!("wtf?");
            };

        let DiffMode { pre, post } = diff;

        for d in [pre, post] {
            for (address, account) in d {
                let AccountState { storage, .. } = account;
                let empty_storage = storage.is_none();
                let mut storage_keys = vec![];
                if let Some(stor) = storage {
                    storage_keys.extend(stor.keys().copied());
                }
                let (proof, storage_proof, _storage_hash, _account_is_empty) = get_proof(
                    address,
                    storage_keys.clone(),
                    (block_number - 1).into(),
                    provider,
                )
                .await?;
                insert_mpt(&mut state_mpt, proof);

                let (next_proof, next_storage_proof, _next_storage_hash, _next_account_is_empty) =
                    get_proof(address, storage_keys, block_number.into(), provider).await?;
                insert_mpt(&mut state_mpt, next_proof);

                let key = keccak(address.0);
                if !empty_storage {
                    let mut storage_mpt = Mpt::new();
                    let storage_mpt = storage_mpts
                        .get_mut(&key.into())
                        .unwrap_or(&mut storage_mpt);
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
                get_proof(w.address, vec![], (block_number - 1).into(), provider).await?;
            insert_mpt(&mut state_mpt, proof);
        }
    }

    let prev_block = provider
        .get_block(block_number - 1)
        .await?
        .ok_or_else(|| anyhow!("Block not found. Block number: {}", block_number - 1))?;
    state_mpt.root = prev_block.state_root;

    let (block_metadata, _final_hash) = get_block_metadata(
        block_number.into(),
        chain_id,
        provider,
        request_miner_from_clique,
    )
    .await?;

    let mut state_mpt = state_mpt.to_partial_trie();
    let mut txns_mpt = HashedPartialTrie::from(Node::Empty);
    let mut receipts_mpt = HashedPartialTrie::from(Node::Empty);
    let mut gas_used = U256::zero();
    let mut bloom: Bloom = Bloom::zero();

    // Withdrawals
    let wds = if let Some(v) = &block.withdrawals {
        v.iter()
            .map(|w| (w.address, w.amount * 1_000_000_000)) // Alchemy returns Gweis for some reason
            .collect()
    } else {
        vec![]
    };

    // Block hashes
    let block_hashes = get_block_hashes(block_number, provider.url().as_ref()).await?;

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
        new_bloom.accrue_bloom(&receipt.logs_bloom);
        let mut new_txns_mpt = txns_mpt.clone();
        new_txns_mpt
            .insert(
                Nibbles::from_bytes_be(&rlp::encode(&receipt.transaction_index)).unwrap(),
                signed_txn.clone(),
            )
            .unwrap();
        let mut new_receipts_mpt = receipts_mpt.clone();
        let mut bytes = rlp::encode(&receipt).to_vec();
        if !receipt.transaction_type.unwrap().is_zero() {
            bytes.insert(0, receipt.transaction_type.unwrap().0[0] as u8);
        }
        new_receipts_mpt
            .insert(
                Nibbles::from_bytes_be(&rlp::encode(&receipt.transaction_index)).unwrap(),
                bytes,
            )
            .unwrap();

        // Use withdrawals for the last tx in the block.
        let _withdrawals = if last_tx { wds.clone() } else { vec![] };
        // For the last tx, we check that the final trie roots match those in the block
        // header.

        let trie_roots_after = if last_tx {
            TrieRoots {
                state_root: block.state_root,
                transactions_root: block.transactions_root,
                receipts_root: block.receipts_root,
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
                storage_tries: trimmed_storage_mpts.into_iter().collect(),
            },
            withdrawals: vec![],
            contract_code: contract_codes.clone(),
            block_metadata: block_metadata.clone(),
            block_hashes: block_hashes.clone(),
            gas_used_before: gas_used,
            gas_used_after: gas_used + receipt.gas_used.unwrap(),
            checkpoint_state_trie_root: prev_block.state_root, // TODO: make it configurable
            trie_roots_after,
            txn_number_before: receipt.transaction_index.0[0].into(),
        };

        state_mpt = next_state_mpt;
        storage_mpts = next_storage_mpts;
        gas_used += receipt.gas_used.unwrap();
        assert_eq!(gas_used, receipt.cumulative_gas_used);
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
                state: create_fully_hashed_out_trie_from_hash(block.state_root),
                txn: create_fully_hashed_out_trie_from_hash(EMPTY_TRIE_HASH),
                receipt: create_fully_hashed_out_trie_from_hash(EMPTY_TRIE_HASH),
                storage: HashMap::default(),
            }
        });

    let initial_extra_data = ExtraBlockData {
        checkpoint_state_trie_root: prev_block.state_root,
        ..Default::default()
    };

    let mut final_tries = PartialTrieState {
        state: state_mpt,
        storage: storage_mpts,
        txn: txns_mpt,
        receipt: receipts_mpt,
    };

    let final_extra_data = proof_gen_ir
        .last()
        .map(|ir| ExtraBlockData {
            checkpoint_state_trie_root: prev_block.state_root,
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

fn create_fully_hashed_out_trie_from_hash(h: TrieRootHash) -> HashedPartialTrie {
    let mut trie = HashedPartialTrie::default();
    trie.insert(Nibbles::default(), h).unwrap();

    trie
}
