use anyhow::{bail, Result};
use evm_arithmetization::GenerationInputs;
use ops::{AggProof, BlockProof, TxProof};
use paladin::{
    directive::{Directive, IndexedStream, Literal},
    runtime::Runtime,
};
use proof_gen::{
    proof_types::{AggregatableProof, GeneratedBlockProof},
    types::PlonkyProofIntern,
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
pub struct ProverInput {
    pub proof_gen_ir: Vec<GenerationInputs>,
}

impl ProverInput {
    pub async fn prove(
        self,
        runtime: &Runtime,
        _previous: Option<PlonkyProofIntern>,
    ) -> Result<GeneratedBlockProof> {
        tracing::info!("Proving block");
        let agg_proof = IndexedStream::from(self.proof_gen_ir)
            .map(&TxProof)
            .fold(&AggProof)
            .run(runtime)
            .await?;

        if let AggregatableProof::Agg(proof) = agg_proof {
            let block_proof = Literal(proof)
                .map(&BlockProof { prev: None })
                .run(runtime)
                .await?;
            tracing::info!("Block proof generated");

            Ok(block_proof.0)
        } else {
            bail!("AggProof is is not GeneratedAggProof")
        }
    }
}
