use ethers::prelude::*;
use ethers::utils::keccak256;

pub fn keccak<T: AsRef<[u8]> + Clone>(bytes: T) -> [u8; 32] {
    keccak256(bytes.clone())
}

pub fn has_storage_deletion(trace: &GethTrace) -> bool {
    let diff = if let GethTrace::Known(GethTraceFrame::PreStateTracer(PreStateFrame::Diff(diff))) =
        trace
    {
        diff
    } else {
        panic!("wtf?");
    };

    for (addr, old) in &diff.pre {
        if !diff.post.contains_key(addr) {
            return true;
        } else {
            let new = diff.post.get(addr).unwrap();
            for &k in old.storage.clone().unwrap_or_default().keys() {
                if !new.storage.clone().unwrap_or_default().contains_key(&k) {
                    return true;
                }
            }
        }
    }
    false
}
