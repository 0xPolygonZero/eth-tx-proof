use anyhow::Context;
use ethers::types::{Address, H256, U256};
use evm_arithmetization::proof::BlockHashes;
use futures::{stream::FuturesOrdered, TryStreamExt};
use reqwest::IntoUrl;
use serde::Deserialize;
use tracing::info;

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct EthGetBlockByNumberResult {
    hash: H256,
    number: U256,
    parent_hash: H256,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Withdrawal {
    address: Address,
    amount: U256,
}

impl From<Withdrawal> for (Address, U256) {
    fn from(v: Withdrawal) -> Self {
        (v.address, v.amount)
    }
}

/// The response from the `eth_getBlockByNumber` RPC method.
#[derive(Deserialize, Debug)]
struct EthGetBlockByNumberResponse {
    result: EthGetBlockByNumberResult,
}

impl EthGetBlockByNumberResponse {
    /// Fetches the block metadata for the given block number.
    async fn fetch<U: IntoUrl>(block_number: u64, rpc_url: U) -> anyhow::Result<Self> {
        let client = reqwest::Client::new();
        let block_number_hex = format!("0x{:x}", block_number);
        info!("Fetching block metadata for block {}", block_number_hex);

        let response = client
            .post(rpc_url)
            .json(&serde_json::json!({
                "jsonrpc": "2.0",
                "method": "eth_getBlockByNumber",
                "params": [&block_number_hex, false],
                "id": 1,
            }))
            .send()
            .await
            .context("fetching eth_getBlockByNumber")?;

        let bytes = response.bytes().await?;
        let des = &mut serde_json::Deserializer::from_slice(&bytes);
        let parsed =
            serde_path_to_error::deserialize(des).context("deserializing eth_getBlockByNumber")?;

        Ok(parsed)
    }

    async fn fetch_previous_block_hashes<U: IntoUrl + Copy>(
        rpc_url: U,
        block_number: u64,
    ) -> anyhow::Result<Vec<H256>> {
        if block_number == 0 {
            return Ok(vec![H256::default(); 256]);
        }

        let mut hashes = Vec::with_capacity(256);

        let padding_delta = block_number as i64 - 256;
        if padding_delta < 0 {
            let default = H256::default();
            for _ in 0..padding_delta.abs() {
                hashes.push(default);
            }
        }

        // Every block response includes the _parent_ hash along with its hash, so we
        // can just fetch half the blocks to acquire all hashes for the range.
        let start = block_number.saturating_sub(256);
        let mut futs: FuturesOrdered<_> = (start..=block_number)
            .step_by(2)
            .map(|block_number| Self::fetch(block_number, rpc_url))
            .collect();

        while let Some(response) = futs.try_next().await? {
            // Ignore hash of the current block.
            if response.result.number == block_number.into() {
                hashes.push(response.result.parent_hash);
                continue;
            }

            // Ignore the parent of the start block.
            if response.result.number != start.into() {
                hashes.push(response.result.parent_hash);
            }

            hashes.push(response.result.hash);
        }

        Ok(hashes)
    }
}

pub(crate) async fn get_block_hashes(block_number: u64, url: &str) -> anyhow::Result<BlockHashes> {
    let curr_block_info = EthGetBlockByNumberResponse::fetch(block_number, url).await?;
    let prev_hashes =
        EthGetBlockByNumberResponse::fetch_previous_block_hashes(url, block_number).await?;

    Ok(BlockHashes {
        prev_hashes,
        cur_hash: curr_block_info.result.hash,
    })
}

/// The response from the `eth_chainId` RPC method.
#[derive(Deserialize, Debug)]
pub(crate) struct EthChainIdResponse {
    pub(crate) result: U256,
}

impl EthChainIdResponse {
    /// Fetches the chain id.
    pub(crate) async fn fetch<U: IntoUrl>(rpc_url: U) -> anyhow::Result<Self> {
        let client = reqwest::Client::new();
        info!("Fetching chain id");

        let response = client
            .post(rpc_url)
            .json(&serde_json::json!({
                "jsonrpc": "2.0",
                "method": "eth_chainId",
                "params": [],
                "id": 1,
            }))
            .send()
            .await
            .context("fetching eth_chainId")?;

        let bytes = response.bytes().await?;
        let des = &mut serde_json::Deserializer::from_slice(&bytes);
        let parsed = serde_path_to_error::deserialize(des).context("deserializing eth_chainId")?;

        Ok(parsed)
    }
}

#[derive(Debug, Deserialize)]
pub(crate) struct CliqueGetSignersAtHashResponse {
    pub(crate) result: CliqueGetSignersAtHashResult,
}

impl CliqueGetSignersAtHashResponse {
    pub(crate) async fn fetch<U: IntoUrl>(rpc_url: U, b_hash: H256) -> anyhow::Result<Self> {
        let client = reqwest::Client::new();
        let b_hash_hex = format!("0x{:x}", b_hash);
        info!("Fetching clique signer for block hash {}", b_hash_hex);

        let response = client
            .post(rpc_url)
            .json(&serde_json::json!({
                "jsonrpc": "2.0",
                "method": "clique_getSignersAtHash",
                "params": [b_hash_hex],
                "id": 1,
            }))
            .send()
            .await
            .context("fetching clique_getSignersAtHash")?;

        let bytes = response.bytes().await?;
        let des = &mut serde_json::Deserializer::from_slice(&bytes);
        let parsed = serde_path_to_error::deserialize(des)
            .context("deserializing clique_getSignersAtHash")?;

        Ok(parsed)
    }
}

#[derive(Debug, Deserialize)]
pub(crate) struct CliqueGetSignersAtHashResult {
    pub(crate) signer: Address,
}
