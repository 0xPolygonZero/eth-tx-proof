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

pub mod compat {
    pub fn h256(_: alloy::primitives::B256) -> primitive_types::H256 {
        todo!()
    }
    pub fn address(_: alloy::primitives::Address) -> ethers::types::Address {
        todo!()
    }
    pub fn u256(_: alloy::primitives::U256) -> primitive_types::U256 {
        todo!()
    }
    pub fn bloom(_: alloy::primitives::Bloom) -> [primitive_types::U256; 8] {
        todo!()
    }
}
