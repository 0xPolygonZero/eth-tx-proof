use common::prover_state::P_STATE;
use ethers::types::Transaction;
use paladin::{
    operation::{FatalError, Monoid, Operation, Result},
    registry, RemoteExecute,
};
use plonky_block_proof_gen::{
    proof_gen::{generate_agg_proof, generate_block_proof, generate_txn_proof},
    proof_types::{AggregatableProof, GeneratedAggProof, GeneratedBlockProof},
    prover_state::ProverState,
};
use protocol_decoder::types::TxnProofGenIR;
use serde::{Deserialize, Serialize};
use sysinfo::{MemoryRefreshKind, System};
use tracing::{info_span, Level};

fn p_state() -> &'static ProverState {
    P_STATE.get().expect("Prover state is not initialized")
}

registry!();

#[derive(Deserialize, Serialize, RemoteExecute)]
pub struct TxProof {
    pub memory_threshold_mb: Option<u64>,
}

impl Operation for TxProof {
    type Input = TxnProofGenIR;
    type Output = AggregatableProof;

    fn execute(&self, input: Self::Input) -> Result<Self::Output> {
        let tx_hash = rlp::decode::<Transaction>(
            input
                .gen_inputs
                .signed_txn
                .as_ref()
                .expect("signed txn is missing"),
        )
        .expect("failed to decode signed transaction")
        .hash;

        let _span = info_span!("generate proof", tx_hash = ?tx_hash).entered();
        tracing::event!(Level::INFO, "generating proof for {:?}", tx_hash);

        if let Some(memory_threshold_mb) = self.memory_threshold_mb {
            tracing::event!(
                Level::INFO,
                "memory threshold set to {} MB",
                memory_threshold_mb
            );
            let mut system = System::new();

            loop {
                system.refresh_memory_specifics(MemoryRefreshKind::new().with_ram());
                let available_ram_mb = system.available_memory() as f64 / (1024.0 * 1024.0);
                if available_ram_mb < memory_threshold_mb as f64 {
                    tracing::event!(
                        Level::INFO,
                        "available RAM ({}MB) is less than memory threshold ({}MB). sleeping for 1s",
                        available_ram_mb,
                        memory_threshold_mb
                    );
                    std::thread::sleep(std::time::Duration::from_secs(1));
                } else {
                    tracing::event!(
                        Level::INFO,
                        "available RAM ({}MB) is greater than memory threshold ({}MB). starting proof generation",
                        available_ram_mb,
                        memory_threshold_mb
                    );
                    break;
                }
            }
        }

        let start = std::time::Instant::now();
        let result = generate_txn_proof(p_state(), input, None).map_err(FatalError::from)?;
        tracing::event!(
            Level::INFO,
            "generate transaction proof for {:?} took {:?}",
            tx_hash,
            start.elapsed()
        );

        Ok(result.into())
    }
}

#[derive(Deserialize, Serialize, RemoteExecute)]
pub struct AggProof;

impl Monoid for AggProof {
    type Elem = AggregatableProof;

    fn combine(&self, a: Self::Elem, b: Self::Elem) -> Result<Self::Elem> {
        let start = std::time::Instant::now();
        let result = generate_agg_proof(p_state(), &a, &b).map_err(FatalError::from)?;
        tracing::info!("generate aggregation proof took {:?}", start.elapsed());

        Ok(result.into())
    }

    fn empty(&self) -> Self::Elem {
        // Expect that empty blocks are padded.
        unimplemented!("empty agg proof")
    }
}

#[derive(Deserialize, Serialize, RemoteExecute)]
pub struct BlockProof {
    pub prev: Option<GeneratedBlockProof>,
}

impl Operation for BlockProof {
    type Input = GeneratedAggProof;
    type Output = GeneratedBlockProof;

    fn execute(&self, input: Self::Input) -> Result<Self::Output> {
        let start = std::time::Instant::now();
        let proof = generate_block_proof(p_state(), self.prev.as_ref(), &input)
            .map_err(FatalError::from)?;
        tracing::info!("generate block proof took {:?}", start.elapsed());

        Ok(proof)
    }
}
