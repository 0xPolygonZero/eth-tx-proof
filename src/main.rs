use anyhow::Result;
use eth_proof::gather_witness_and_prove_tx;
use eth_proof::utils::init_env_logger;
use ethers::prelude::*;
use std::convert::TryFrom;
use std::str::FromStr;

#[tokio::main]
async fn main() -> Result<()> {
    init_env_logger();
    let rpc_url = std::env::var("RPC_URL")?;
    let provider = Provider::<Http>::try_from(&rpc_url)?;

    let args = std::env::args().collect::<Vec<_>>();
    println!("Proving tx {}", args[1]);
    let tx =
        provider
            .get_transaction(TxHash::from_str(&args[1]).unwrap())
            .await?
            .expect("Tx not found.");
    gather_witness_and_prove_tx(tx, &provider).await?;

    Ok(())
}
