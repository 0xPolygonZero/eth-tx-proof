use ethers::prelude::*;
use ethers::utils::keccak256;

pub fn keccak<T: AsRef<[u8]> + Clone>(bytes: T) -> [u8; 32] {
    keccak256(bytes.clone())
}

pub fn keccak_if_long_enough<T: AsRef<[u8]> + Clone>(bytes: T) -> [u8; 32] {
    match bytes.as_ref().len() <= 32 {
        true => {
            let mut padded_bytes: [u8; 32] = Default::default();
            padded_bytes[32 - bytes.as_ref().len()..].copy_from_slice(bytes.as_ref());
            tracing::debug!("Uno chiquichico = {:?}", padded_bytes);
            padded_bytes
        }

        false => keccak(bytes),
    }
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
