use anyhow::Result;
use evm_arithmetization::GenerationInputs;
use futures::TryStreamExt;
use ops::TxProof;
use paladin::{
    directive::{Directive, IndexedStream},
    runtime::Runtime,
};
use proof_gen::{proof_types::GeneratedBlockProof, types::PlonkyProofIntern};
use serde::{Deserialize, Serialize};
use tracing::info;

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
        let b_number = self.proof_gen_ir[0].block_metadata.block_number;
        tracing::info!("Generating witness for block {:?}", b_number);

        use mpt_trie::partial_trie::PartialTrie;

        IndexedStream::from(self.proof_gen_ir)
            .map(&TxProof)
            .run(runtime)
            .await?
            .try_collect::<Vec<_>>()
            .await?;

        info!("Successfully generated witness for block {:?}!", b_number);

        // Dummy proof to match expected output type.
        Ok(GeneratedBlockProof {
            b_height: b_number.as_u64(),
            intern: proof_gen::proof_gen::dummy_proof()?,
        })
    }
}
