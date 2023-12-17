use std::convert::TryFrom;
use std::io::{Read, Write};

use anyhow::Result;
use clap::Parser;
use common::prover_state::set_prover_state_from_config;
use dotenvy::dotenv;
use ethers::prelude::*;
use leader::gather_witness;
use leader::utils::init_env_logger;

mod cli;
mod prover;
use cli::Command;
use ops::register;
use paladin::runtime::Runtime;
use protocol_decoder::types::TxnProofGenIR;

#[tokio::main]
async fn main() -> Result<()> {
    dotenv().ok();
    init_env_logger();
    let args = cli::Cli::parse();

    if let paladin::config::Runtime::InMemory = args.paladin.runtime {
        // If running in emulation mode, we'll need to initialize the prover
        // state here.
        if set_prover_state_from_config(args.prover_state_config.into()).is_err() {
            log::warn!(
                "prover state already set. check the program logic to ensure it is only set once"
            );
        }
    }

    let runtime = Runtime::from_config(&args.paladin, register()).await?;

    match args.command {
        Command::Rpc {
            rpc_url,
            transaction_hash,
        } => {
            let provider = Provider::<Http>::try_from(&rpc_url)?;

            let gen_inputs = gather_witness(transaction_hash, &provider).await?;
            std::io::stdout().write_all(&serde_json::to_vec(&gen_inputs)?)?;
        }
        Command::Prove { input_witness } => {
            let mut file = std::fs::File::open(&input_witness)?;
            let mut buffer = String::new();
            file.read_to_string(&mut buffer)?;
            let proof_gen_ir: Vec<TxnProofGenIR> = serde_json::from_str(&buffer)?;
            let prover_input = prover::ProverInput { proof_gen_ir };
            let proof = prover_input.prove(&runtime, None).await?;
            std::io::stdout().write_all(&serde_json::to_vec(&proof)?)?;
        }
        Command::GenerateAndProve {
            rpc_url,
            transaction_hash,
        } => {
            unimplemented!()
        }
    }

    Ok(())
}
