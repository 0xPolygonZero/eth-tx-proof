use alloy::{
    primitives::B256,
    rpc::types::trace::geth::{GethTrace, PreStateFrame},
};

pub fn keccak<T: AsRef<[u8]> + Clone>(bytes: T) -> B256 {
    alloy::primitives::keccak256(bytes)
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
/// [`ethers`](__ethers_for_compat) etc.
///
/// Migrating our dependencies is tracked by [zk_evm#226](https://github.com/0xPolygonZero/zk_evm/issues/229)
pub mod compat {
    use alloy::primitives::FixedBytes;

    pub fn h256(FixedBytes(it): alloy::primitives::B256) -> __primitive_types_for_compat::H256 {
        __primitive_types_for_compat::H256(it)
    }
    pub fn address(
        alloy::primitives::Address(FixedBytes(it)): alloy::primitives::Address,
    ) -> __ethers_for_compat::types::Address {
        __primitive_types_for_compat::H160(it)
    }
    pub fn u256(it: alloy::primitives::U256) -> __primitive_types_for_compat::U256 {
        __primitive_types_for_compat::U256::from_big_endian(&it.to_be_bytes::<32>())
    }
    pub fn bloom(
        alloy::primitives::Bloom(FixedBytes(it)): alloy::primitives::Bloom,
    ) -> [__primitive_types_for_compat::U256; 8] {
        // have 8 * 256, want 256 * 8, (no unsafe, no unstable)
        // TODO(aatifsyed): we're going from unintepreted bytes to an integer type
        //                  is this right?
        let mut out = [__primitive_types_for_compat::U256::zero(); 8];
        let chunks = it.chunks(32);
        assert_eq!(chunks.len(), 8);
        for (ix, chunk) in chunks.enumerate() {
            let mut a = [0; 32];
            a.copy_from_slice(chunk);
            out[ix] = __primitive_types_for_compat::U256::from(a);
        }
        out
    }
}
