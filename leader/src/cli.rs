use std::path::PathBuf;

use clap::{Parser, Subcommand, ValueHint};
use common::prover_state::cli::CliProverStateConfig;
use ethers::types::TxHash;

#[derive(Parser)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
    /// Worker memory threshold for transaction proofs, in MB.
    #[arg(long, short, env = "MEMORY_THRESHOLD_MB")]
    pub memory_threshold_mb: Option<u64>,
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
