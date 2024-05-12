mod cli;
mod prover;
use cli::Command;
use ops::register;
use paladin::runtime::Runtime;
mod init;

use std::fs::File;

use anyhow::Result;
use clap::Parser;
use common::prover_state::set_prover_state_from_config;
use dotenvy::dotenv;
use leader::gather_witness;

#[tokio::main]
async fn main() -> Result<()> {
    dotenv().ok();
    init::tracing();

    let args = cli::Cli::parse();

    match args.command {
        Command::Rpc {
            rpc_url,
            transaction_hash,
            request_miner_from_clique,
        } => {
            let provider = alloy::providers::RootProvider::new_http(rpc_url);
            let gen_inputs =
                gather_witness(transaction_hash, &provider, request_miner_from_clique).await?;
            println!("{}", serde_json::to_string(&gen_inputs)?);
        }
        Command::Prove {
            input_witness,
            paladin,
            prover_state_config,
        } => {
            if let paladin::config::Runtime::InMemory = paladin.runtime {
                // If running in emulation mode, we'll need to initialize the prover
                // state here.
                if set_prover_state_from_config(prover_state_config.into()).is_err() {
                    tracing::warn!(
                        "prover state already set. check the program logic to ensure it is only set once"
                    );
                }
            }

            let prover_input = prover::ProverInput {
                proof_gen_ir: serde_json::from_reader(File::open(input_witness)?)?,
            };
            let runtime = Runtime::from_config(&paladin, register()).await?;
            let proof = prover_input.prove(&runtime, None).await?;
            println!("{}", serde_json::to_string(&proof)?);
            runtime.close().await?;
        }
    }

    Ok(())
}
