use std::convert::TryFrom;
use std::io::{Read, Write};

use anyhow::Result;
use clap::Parser;
use common::prover_state::set_prover_state_from_config;
use dotenvy::dotenv;
use ethers::prelude::*;
use leader::gather_witness;

mod cli;
mod prover;
use cli::Command;
use ops::register;
use paladin::runtime::Runtime;
use trace_decoder::types::TxnProofGenIR;
mod init;

#[tokio::main]
async fn main() -> Result<()> {
    dotenv().ok();
    init::tracing();

    let args = cli::Cli::parse();

    match args.command {
        Command::Rpc {
            rpc_url,
            block_number,
            request_miner_from_clique,
        } => {
            let provider = Provider::<Http>::try_from(&rpc_url)?;

            let gen_inputs =
                gather_witness(block_number, &provider, request_miner_from_clique).await?;
            use mpt_trie::partial_trie::PartialTrie;
            tracing::debug!(
                "las txns = {:?}, y su hash = {:?}",
                gen_inputs[0].tries.transactions_trie,
                gen_inputs[0].tries.transactions_trie.hash()
            );
            std::fs::write(
                format!("{:?}.json", gen_inputs[0].block_metadata.block_number),
                &serde_json::to_vec(&gen_inputs)?,
            )?;
            tracing::debug!("the state trie = {:#?}", gen_inputs[0].tries.state_trie);
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
            let proof_gen_ir: Vec<TxnProofGenIR> = serde_json::from_str(&buffer)?;
            let prover_input = prover::ProverInput { proof_gen_ir };
            let runtime = Runtime::from_config(&paladin, register()).await?;
            let proof = prover_input.prove(&runtime, None).await?;
            std::io::stdout().write_all(&serde_json::to_vec(&proof)?)?;
            runtime.close().await?;
        }
    }

    Ok(())
}
