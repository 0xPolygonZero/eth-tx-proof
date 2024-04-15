use anyhow::Result;
use futures::TryStreamExt;
use ops::TxProof;
use paladin::{
    directive::{Directive, IndexedStream},
    runtime::Runtime,
};
use proof_gen::{proof_types::GeneratedBlockProof, types::PlonkyProofIntern};
use serde::{Deserialize, Serialize};
use trace_decoder::types::TxnProofGenIR;
use tracing::info;

#[derive(Debug, Deserialize, Serialize)]
pub struct ProverInput {
    pub proof_gen_ir: Vec<TxnProofGenIR>,
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
        tracing::debug!(
            "txn tries un hashes = {:#?}",
            self.proof_gen_ir
                .iter()
                .map(|inputs| (
                    inputs.tries.transactions_trie.clone(),
                    inputs.tries.transactions_trie.hash()
                ))
                .collect::<Vec<_>>()
        );

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
