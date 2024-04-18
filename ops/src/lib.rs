use common::prover_state::P_STATE;
use ethers::types::Transaction;
use evm_arithmetization::GenerationInputs;
use paladin::{
    operation::{FatalError, Monoid, Operation, Result},
    registry, RemoteExecute,
};
use proof_gen::{
    proof_gen::{generate_agg_proof, generate_block_proof, generate_txn_proof},
    proof_types::{AggregatableProof, GeneratedAggProof, GeneratedBlockProof},
    prover_state::ProverState,
};
use serde::{Deserialize, Serialize};
use tracing::{info_span, Level};

fn p_state() -> &'static ProverState {
    P_STATE.get().expect("Prover state is not initialized")
}

registry!();

#[derive(Deserialize, Serialize, RemoteExecute)]
pub struct TxProof;

impl Operation for TxProof {
    type Input = GenerationInputs;
    type Output = AggregatableProof;

    fn execute(&self, input: Self::Input) -> Result<Self::Output> {
        // If we hit a dummy txn, there is no signed txn, so we must come up with a
        // backup identifier to use for logging.
        let tx_ident = input
            .signed_txn
            .as_ref()
            .map(|txn| {
                rlp::decode::<Transaction>(txn)
                    .expect("failed to decode signed transaction")
                    .hash
                    .to_string()
            })
            .unwrap_or_else(|| {
                format!(
                    "Dummy txn for block {} at {}",
                    input.block_metadata.block_number, input.txn_number_before
                )
            });

        let _span = info_span!("generate proof", tx_hash = ?tx_ident).entered();
        tracing::event!(Level::INFO, "generating proof for {:?}", tx_ident);

        let start = std::time::Instant::now();
        let result = generate_txn_proof(p_state(), input, None).map_err(FatalError::from)?;
        tracing::event!(
            Level::INFO,
            "generate transaction proof for {:?} took {:?}",
            tx_ident,
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
