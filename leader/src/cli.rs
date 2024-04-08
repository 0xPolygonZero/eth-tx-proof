use std::path::PathBuf;

use clap::{Parser, Subcommand, ValueHint};
use common::prover_state::cli::CliProverStateConfig;
use ethers::types::TxHash;

#[derive(Parser)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Generates the witness and outputs it to stdout.
    Rpc {
        /// The RPC URL.
        #[arg(long, short = 'u', value_hint = ValueHint::Url, env = "RPC_URL")]
        rpc_url: String,
        /// The transaction hash from which to generate the witness.
        #[arg(long, short)]
        transaction_hash: TxHash,

        /// If enabled, we will instead attempt to get the block miner from
        /// clique.
        #[arg(long, short)]
        request_miner_from_clique: bool,
    },
    /// Generates a proof from the given witness and outputs it to stdout.
    Prove {
        /// The path to the witness file.
        #[arg(long, short, value_hint = ValueHint::FilePath)]
        input_witness: PathBuf,
        #[clap(flatten)]
        paladin: paladin::config::Config,
        // Note this is only relevant for the leader when running in in-memory
        // mode.
        #[clap(flatten)]
        prover_state_config: CliProverStateConfig,
    },
}
