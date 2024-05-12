use alloy::{
    primitives::{FixedBytes, B256},
    rpc::types::trace::geth::{GethTrace, PreStateFrame},
};

pub fn keccak<T: AsRef<[u8]> + Clone>(bytes: T) -> B256 {
    FixedBytes(ethers::utils::keccak256(bytes.clone()))
}

pub fn has_storage_deletion(trace: &GethTrace) -> bool {
    let GethTrace::PreStateTracer(PreStateFrame::Diff(diff)) = trace else {
        panic!()
    };

    for (addr, old) in &diff.pre {
        if !diff.post.contains_key(addr) {
            return true;
        } else {
            let new = diff.post.get(addr).unwrap();
            for &k in old.storage.clone().keys() {
                if !new.storage.clone().contains_key(&k) {
                    return true;
                }
            }
        }
    }
    false
}
/// This crate wants to use [`alloy`], but [`evm_arithmetization`] uses
/// [`ethers`] etc. Migrating our dependencies is tracked by TODO(aatifsyed)
pub mod compat {
    use std::array;

    use alloy::primitives::FixedBytes;

    pub fn h256(FixedBytes(it): alloy::primitives::B256) -> primitive_types::H256 {
        primitive_types::H256(it)
    }
    pub fn address(
        alloy::primitives::Address(FixedBytes(it)): alloy::primitives::Address,
    ) -> ethers::types::Address {
        primitive_types::H160(it)
    }
    pub fn u256(it: alloy::primitives::U256) -> primitive_types::U256 {
        primitive_types::U256::from_big_endian(&it.to_be_bytes::<32>())
    }
    pub fn bloom(
        alloy::primitives::Bloom(FixedBytes(it)): alloy::primitives::Bloom,
    ) -> [primitive_types::U256; 8] {
        // have 8 * 256, want 256 * 8, (no unsafe, no unstable)
        // TODO(aatifsyed): we're going from unintepreted bytes to an integer type
        //                  is this right?
        let mut chunks = it.chunks_exact(32);
        array::from_fn(|_ix| {
            primitive_types::U256::from(<[u8; 32]>::try_from(chunks.next().unwrap()).unwrap())
        })
    }
}
