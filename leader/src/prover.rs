use std::sync::mpsc::channel;

use anyhow::{bail, Result};
use ops::{AggProof, AggregatableProofWithIdentity, BlockProof, TxProof};
use paladin::{
    directive::{Directive, IndexedStream, Literal},
    operation::{Monoid, Operation},
    runtime::Runtime,
};
use plonky_block_proof_gen::{
    proof_types::{AggregatableProof, GeneratedBlockProof},
    types::PlonkyProofIntern,
};
use protocol_decoder::types::TxnProofGenIR;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use threadpool::ThreadPool;

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
        tracing::info!("Proving block");
        let agg_proof = IndexedStream::from(self.proof_gen_ir)
            .map(&TxProof)
            .fold(&AggProof)
            .run(runtime)
            .await?;

        if let AggregatableProofWithIdentity::Agg(AggregatableProof::Agg(proof)) = agg_proof {
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

    pub fn prove_in_memory(self, parallelism: usize) -> Result<GeneratedBlockProof> {
        tracing::info!("Proving block");

        let (tx, rx) = channel();
        let pool = ThreadPool::new(parallelism);
        let job_size = self.proof_gen_ir.len();
        for (idx, tx_ir) in self.proof_gen_ir.into_iter().enumerate() {
            let tx = tx.clone();
            pool.execute(move || {
                let agg_proof = TxProof.execute(tx_ir).unwrap();
                tx.send((idx, agg_proof)).unwrap();
            });
        }

        let mut tx_proofs: Vec<_> = rx.iter().take(job_size).collect();
        tx_proofs.sort_by_key(|(idx, _)| *idx);

        let agg_proof = tx_proofs.into_par_iter().map(|(_, p)| p).reduce(
            || AggregatableProofWithIdentity::Unit,
            |a, b| AggProof.combine(a, b).unwrap(),
        );

        if let AggregatableProofWithIdentity::Agg(AggregatableProof::Agg(proof)) = agg_proof {
            let b_proof = BlockProof { prev: None };
            let block_proof = b_proof.execute(proof).unwrap();
            tracing::info!("Block proof generated");

            Ok(block_proof)
        } else {
            bail!("AggProof is is not GeneratedAggProof")
        }
    }
}
