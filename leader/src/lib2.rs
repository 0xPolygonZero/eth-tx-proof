use alloy::{
    primitives::TxHash,
    providers::{ext::DebugApi as _, Network, Provider},
    rpc::types::{
        eth::Block,
        trace::geth::{
            DiffMode, GethDebugBuiltInTracerType, GethDebugTracerConfig, GethDebugTracerType,
            GethDebugTracingOptions, GethTrace, PreStateConfig, PreStateFrame, PreStateMode,
        },
    },
    transports::Transport,
};
use anyhow::{bail, Context as _};

const BLOCK_WITH_FULL_TRANSACTIONS: bool = true;
const BLOCK_WITHOUT_FULL_TRANSACTIONS: bool = false;

pub struct Gathered {
    block: Block,
}

pub async fn gather<ProviderT, TransportT>(
    tx: TxHash,
    provider: ProviderT,
    request_miner_from_clique: bool,
) -> anyhow::Result<()>
where
    ProviderT: Provider<TransportT>,
    TransportT: Clone + Transport,
{
    let tx = provider
        .get_transaction_by_hash(tx)
        .await
        .context("couldn't get root transaction")?;
    let block_number = tx.block_number.context("transaction has no block number")?;
    let tx_index = tx
        .transaction_index
        .and_then(|it| usize::try_from(it).ok())
        .context("absent or out-of-bounds transaction index")?;
    let block = provider
        .get_block(block_number.into(), BLOCK_WITH_FULL_TRANSACTIONS)
        .await
        .context("couldn't get block")?
        .context("no such block")?;

    let chain_id = provider
        .get_chain_id()
        .await
        .context("couldn't get chain id")?;

    for (transaction_ix, transaction_hash) in
        block.transactions.hashes().take(tx_index + 1).enumerate()
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

    provider.get_block(block_number.into(), BLOCK_WITHOUT_FULL_TRANSACTIONS);

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

async fn thing1<ProviderT, TransportT>(
    provider: &ProviderT,
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
