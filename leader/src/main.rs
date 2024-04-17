use std::convert::TryFrom;
use std::io::{Read, Write};

use anyhow::Result;
use clap::Parser;
use common::prover_state::set_prover_state_from_config;
use dotenvy::dotenv;
use ethers::prelude::*;
use evm_arithmetization::GenerationInputs;
use leader::gather_witness;

mod cli;
mod prover;
use cli::Command;
use ops::register;
use paladin::runtime::Runtime;
mod init;

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
            let provider = Provider::<Http>::try_from(&rpc_url)?;

            let gen_inputs =
                gather_witness(transaction_hash, &provider, request_miner_from_clique).await?;
            std::io::stdout().write_all(&serde_json::to_vec(&gen_inputs)?)?;
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

            let mut file = std::fs::File::open(&input_witness)?;
            let mut buffer = String::new();
            file.read_to_string(&mut buffer)?;
            let proof_gen_ir: Vec<GenerationInputs> = serde_json::from_str(&buffer)?;
            let prover_input = prover::ProverInput { proof_gen_ir };
            let runtime = Runtime::from_config(&paladin, register()).await?;
            let proof = prover_input.prove(&runtime, None).await?;
            std::io::stdout().write_all(&serde_json::to_vec(&proof)?)?;
            runtime.close().await?;
        }
    }

    Ok(())
}
