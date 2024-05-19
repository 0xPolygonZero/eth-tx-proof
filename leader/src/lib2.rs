use std::collections::BTreeMap;

use alloy::{
    primitives::{Address, TxHash, B256},
    providers::{ext::DebugApi as _, Provider},
    rpc::types::{
        eth::{Block, BlockTransactions, EIP1186AccountProofResponse, Transaction},
        trace::geth::{
            AccountState, DiffMode, GethDebugBuiltInTracerType, GethDebugTracerConfig,
            GethDebugTracerType, GethDebugTracingOptions, GethTrace, PreStateConfig, PreStateFrame,
            PreStateMode,
        },
    },
    transports::Transport,
};
use anyhow::{bail, ensure, Context as _};
use futures::{FutureExt as _, StreamExt as _, TryFutureExt as _, TryStreamExt as _};

const BLOCK_WITH_FULL_TRANSACTIONS: bool = true;
const BLOCK_WITHOUT_FULL_TRANSACTIONS: bool = false;

pub struct Gathered {
    root_transaction: Transaction,
    root_block: Block,
}

pub async fn gather<ProviderT, TransportT>(
    target_transaction: TxHash,
    provider: ProviderT,
    request_miner_from_clique: bool,
) -> anyhow::Result<()>
where
    ProviderT: Provider<TransportT>,
    TransportT: Clone + Transport,
{
    // 1. Get the target transaction
    let target_transaction = provider
        .get_transaction_by_hash(target_transaction)
        .await
        .context("couldn't get root transaction")?;

    // 2. Get the block that contains that transaction
    let block_number = target_transaction
        .block_number
        .context("transaction has no block number")?;
    let block = provider
        .get_block(block_number.into(), BLOCK_WITH_FULL_TRANSACTIONS)
        .await
        .context("couldn't get block")?
        .context("no such block")?;

    // 3. Get the preceding transactions
    let mut all_transactions_in_block = match block.transactions.clone() {
        BlockTransactions::Full(it) => it,
        other => bail!("expected full transactions, got {:?}", other),
    };
    let target_transaction_index = target_transaction
        .transaction_index
        .and_then(|it| usize::try_from(it).ok())
        .context("absent or out-of-bounds transaction index")?;
    ensure!(
        all_transactions_in_block
            .get(target_transaction_index)
            .is_some_and(|it| *it == target_transaction),
        "inconsistent block"
    );
    all_transactions_in_block.truncate(target_transaction_index);
    let preceding_transactions = all_transactions_in_block;

    // 3. For each preceding transaction in the block
    for (transaction_ix, transaction_hash) in block
        .transactions
        .hashes()
        .take(target_transaction_index + 1)
        .enumerate()
    {
        let transaction = provider
            .get_transaction_by_hash(*transaction_hash)
            .await
            .context("couldn't get transaction")?;
        thing1(&provider, transaction_hash, block_number).await?;
        thing2(&provider, transaction_hash, block_number).await?;
    }

    for withdrawal in block.withdrawals.iter().flatten() {
        let withdrawal_proof = provider
            .get_proof(withdrawal.address, vec![], (block_number - 1).into())
            .await
            .context("couldn't get proof for withdrawal")?;
    }

    let mut prev_hashes = [B256::ZERO; 256];
    let concurrency = prev_hashes.len();
    futures::stream::iter(
        prev_hashes
            .iter_mut()
            .rev()
            .zip(std::iter::successors(Some(block_number), |it| {
                it.checked_sub(1)
            }))
            .map(|(dst, block_number)| {
                let provider = &provider;
                async move {
                    let block = provider
                        .get_block(block_number.into(), BLOCK_WITHOUT_FULL_TRANSACTIONS)
                        .await
                        .context("couldn't get block")?
                        .context("no such block")?;
                    *dst = block.header.parent_hash;
                    anyhow::Ok(())
                }
            }),
    )
    .buffered(concurrency)
    .try_collect::<()>()
    .await
    .context("couldn't fill previous hashes")?;

    todo!()
}

async fn thing2<ProviderT, TransportT>(
    provider: &ProviderT,
    transaction_hash: &alloy::primitives::FixedBytes<32>,
    block_number: u64,
) -> Result<(), anyhow::Error>
where
    ProviderT: Provider<TransportT>,
    TransportT: Transport + Clone,
{
    let trace = provider
        .debug_trace_transaction(
            *transaction_hash,
            GethDebugTracingOptions {
                tracer: Some(GethDebugTracerType::BuiltInTracer(
                    GethDebugBuiltInTracerType::PreStateTracer,
                )),
                tracer_config: GethDebugTracerConfig(
                    serde_json::to_value(PreStateConfig {
                        diff_mode: Some(true),
                    })
                    .unwrap(),
                ),
                ..Default::default()
            },
        )
        .await
        .context("couldn't debug trace transaction (with diff)")?;
    let DiffMode { post, pre } = match trace {
        GethTrace::PreStateTracer(PreStateFrame::Diff(it)) => it,
        other => bail!("inconsistent trace: {:?}", other),
    };
    for (address, account_state) in pre.into_iter().chain(post) {
        let storage_keys = account_state.storage.keys().copied().collect::<Vec<_>>();
        let previous_proof = provider
            .get_proof(address, storage_keys.clone(), (block_number - 1).into())
            .await
            .context("couldn't get previous proof")?;
        let next_proof = provider
            .get_proof(address, storage_keys, block_number.into())
            .await
            .context("couldn't get next proof")?;
    }
    Ok(())
}

pub struct TracedTransaction {
    transaction: Transaction,
    /// Proof is retrieved from the _previous_ block
    pre_state_accounts_and_proofs: BTreeMap<Address, (AccountState, EIP1186AccountProofResponse)>,
    diff_pre_accounts_and_proofs: BTreeMap<
        Address,
        (
            AccountState,
            EIP1186AccountProofResponse, // from the _previous_ block
            EIP1186AccountProofResponse, // from the target block
        ),
    >,
    diff_post_accounts_and_proofs: BTreeMap<
        Address,
        (
            AccountState,
            EIP1186AccountProofResponse, // from the _previous_ block
            EIP1186AccountProofResponse, // from the target block
        ),
    >,
}

async fn thing1<ProviderT, TransportT>(
    provider: ProviderT,
    transaction_hash: &alloy::primitives::FixedBytes<32>,
    block_number: u64,
) -> Result<(), anyhow::Error>
where
    ProviderT: Provider<TransportT>,
    TransportT: Clone + Transport,
{
    let trace = provider
        .debug_trace_transaction(
            *transaction_hash,
            GethDebugTracingOptions {
                tracer: Some(GethDebugTracerType::BuiltInTracer(
                    GethDebugBuiltInTracerType::PreStateTracer,
                )),
                ..Default::default()
            },
        )
        .await
        .context("couldn't debug trace transaction (without diff)")?;
    let PreStateMode(accounts) = match trace {
        GethTrace::PreStateTracer(PreStateFrame::Default(it)) => it,
        other => bail!("inconsistent trace: {:?}", other),
    };
    for (address, account_state) in accounts {
        let proof = provider
            .get_proof(
                address,
                account_state.storage.keys().copied().collect(),
                (block_number - 1).into(),
            )
            .await
            .context("couldn't get proof")?;
    }
    Ok(())
}
