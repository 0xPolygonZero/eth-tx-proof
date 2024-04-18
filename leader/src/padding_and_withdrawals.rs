use std::{collections::HashMap, iter::empty};

use ethers::{
    types::{Address, H256, U256},
    utils::rlp,
};
use evm_arithmetization::{
    generation::{mpt::AccountRlp, TrieInputs},
    proof::{BlockHashes, BlockMetadata, ExtraBlockData, TrieRoots},
    GenerationInputs,
};
use mpt_trie::partial_trie::PartialTrie;
use mpt_trie::{
    nibbles::Nibbles, partial_trie::HashedPartialTrie, trie_subsets::create_trie_subset,
};
use trace_decoder::types::HashedAccountAddr;

use crate::{utils::keccak, PartialTrieState};

#[derive(Debug)]
pub(crate) struct BlockMetaAndHashes {
    /// All block data excluding block hashes and withdrawals.
    pub b_meta: BlockMetadata,
    /// Block hashes: the previous 256 block hashes and the current block hash.
    pub b_hashes: BlockHashes,
}

/// Pads a generated IR vec with additional "dummy" entries if needed.
/// We need to ensure that generated IR always has at least `2` elements,
/// and if there are only `0` or `1` elements, then we need to pad so
/// that we have two entries in total. These dummy entries serve only to
/// allow the proof generation process to finish. Specifically, we need
/// at least two entries to generate an agg proof, and we need an agg
/// proof to generate a block proof. These entries do not mutate state
/// (unless there are withdrawals in the block (see
/// `[add_withdrawals_to_txns]`), where the final one will mutate the
/// state trie.
pub(crate) fn pad_gen_inputs_with_dummy_inputs_if_needed(
    gen_inputs: &mut Vec<GenerationInputs>,
    other_data: &BlockMetaAndHashes,
    final_extra_data: &ExtraBlockData,
    initial_extra_data: &ExtraBlockData,
    initial_tries: &PartialTrieState,
    final_tries: &PartialTrieState,
    has_withdrawals: bool,
) {
    match gen_inputs.len() {
        0 => {
            debug_assert!(initial_tries.state == final_tries.state);
            debug_assert!(initial_extra_data == final_extra_data);
            // We need to pad with two dummy entries.
            gen_inputs.extend(create_dummy_txn_pair_for_empty_block(
                other_data,
                final_extra_data,
                initial_tries,
            ));
        }
        1 => {
            // We just need one dummy entry.
            // If there are withdrawals, we will need to append them at the end of the block
            // execution, in which case we directly append the dummy proof
            // after the only txn of this block.
            // If there are no withdrawals, then the dummy proof will be prepended to the
            // actual txn.
            match has_withdrawals {
                false => {
                    let dummy_txn =
                        create_dummy_gen_input(other_data, initial_extra_data, initial_tries);
                    gen_inputs.insert(0, dummy_txn)
                }
                true => {
                    let dummy_txn =
                        create_dummy_gen_input(other_data, final_extra_data, final_tries);
                    gen_inputs.push(dummy_txn)
                }
            };
        }
        _ => (),
    }
}

/// The withdrawals are always in the final ir payload. How they are placed
/// differs based on whether or not there are already dummy proofs present
/// in the IR. The rules for adding withdrawals to the IR list are:
/// - If dummy proofs are already present, then the withdrawals are added to the
///   last dummy proof (always index `1`).
/// - If no dummy proofs are already present, then a dummy proof that just
///   contains the withdrawals is appended to the end of the IR vec.
pub(crate) fn add_withdrawals_to_txns(
    txn_ir: &mut [GenerationInputs],
    final_trie_state: &mut PartialTrieState,
    withdrawals: Vec<(Address, U256)>,
) {
    if withdrawals.is_empty() {
        return;
    }

    let withdrawals_with_hashed_addrs_iter = withdrawals
        .iter()
        .map(|(addr, v)| (*addr, hash(addr.as_bytes()), *v));

    update_trie_state_from_withdrawals(
        withdrawals_with_hashed_addrs_iter,
        &mut final_trie_state.state,
    );

    let last_inputs = txn_ir
        .last_mut()
        .expect("We cannot have an empty list of payloads.");

    last_inputs.withdrawals = withdrawals;
    last_inputs.trie_roots_after.state_root = final_trie_state.state.hash();
}

/// Withdrawals update balances in the account trie, so we need to update
/// our local trie state.
fn update_trie_state_from_withdrawals<'a>(
    withdrawals: impl IntoIterator<Item = (Address, HashedAccountAddr, U256)> + 'a,
    state: &mut HashedPartialTrie,
) {
    for (_addr, h_addr, amt) in withdrawals {
        let h_addr_nibs = Nibbles::from_h256_be(h_addr);

        let acc_bytes = state.get(h_addr_nibs).unwrap();

        let mut acc_data = rlp::decode::<AccountRlp>(acc_bytes).unwrap();

        acc_data.balance += amt;

        state
            .insert(h_addr_nibs, rlp::encode(&acc_data).to_vec())
            .unwrap();
    }
}

fn create_dummy_txn_pair_for_empty_block(
    other_data: &BlockMetaAndHashes,
    extra_data: &ExtraBlockData,
    final_tries: &PartialTrieState,
) -> [GenerationInputs; 2] {
    [
        create_dummy_gen_input(other_data, extra_data, final_tries),
        create_dummy_gen_input(other_data, extra_data, final_tries),
    ]
}

fn create_dummy_gen_input(
    other_data: &BlockMetaAndHashes,
    extra_data: &ExtraBlockData,
    tries: &PartialTrieState,
) -> GenerationInputs {
    let sub_tries = create_dummy_proof_trie_inputs(
        tries,
        create_fully_hashed_out_sub_partial_trie(&tries.state),
    );
    create_dummy_gen_input_common(other_data, extra_data, sub_tries)
}

fn create_dummy_gen_input_common(
    other_data: &BlockMetaAndHashes,
    extra_data: &ExtraBlockData,
    sub_tries: TrieInputs,
) -> GenerationInputs {
    let trie_roots_after = TrieRoots {
        state_root: sub_tries.state_trie.hash(),
        transactions_root: sub_tries.transactions_trie.hash(),
        receipts_root: sub_tries.receipts_trie.hash(),
    };

    // Sanity checks
    assert_eq!(
        extra_data.txn_number_before, extra_data.txn_number_after,
        "Txn numbers before/after differ in a dummy payload with no txn!"
    );
    assert_eq!(
        extra_data.gas_used_before, extra_data.gas_used_after,
        "Gas used before/after differ in a dummy payload with no txn!"
    );

    GenerationInputs {
        signed_txn: None,
        tries: sub_tries,
        trie_roots_after,
        checkpoint_state_trie_root: extra_data.checkpoint_state_trie_root,
        block_metadata: other_data.b_meta.clone(),
        block_hashes: other_data.b_hashes.clone(),
        txn_number_before: extra_data.txn_number_before,
        gas_used_before: extra_data.gas_used_before,
        gas_used_after: extra_data.gas_used_after,
        contract_code: HashMap::default(),
        withdrawals: vec![], // this is set after creating dummy payloads
    }
}

fn create_dummy_proof_trie_inputs(
    final_tries_at_end_of_block: &PartialTrieState,
    state_trie_hashed_for_withdrawals: HashedPartialTrie,
) -> TrieInputs {
    let partial_sub_storage_tries: Vec<_> = final_tries_at_end_of_block
        .storage
        .iter()
        .map(|(hashed_acc_addr, s_trie)| {
            (
                *hashed_acc_addr,
                create_fully_hashed_out_sub_partial_trie(s_trie),
            )
        })
        .collect();

    TrieInputs {
        state_trie: state_trie_hashed_for_withdrawals,
        transactions_trie: create_fully_hashed_out_sub_partial_trie(
            &final_tries_at_end_of_block.txn,
        ),
        receipts_trie: create_fully_hashed_out_sub_partial_trie(
            &final_tries_at_end_of_block.receipt,
        ),
        storage_tries: partial_sub_storage_tries,
    }
}

// We really want to get a trie with just a hash node here, and this is an easy
// way to do it.
fn create_fully_hashed_out_sub_partial_trie(trie: &HashedPartialTrie) -> HashedPartialTrie {
    // Impossible to actually fail with an empty iter.
    create_trie_subset(trie, empty::<Nibbles>()).unwrap()
}

fn hash(bytes: &[u8]) -> H256 {
    H256::from(keccak(bytes))
}
