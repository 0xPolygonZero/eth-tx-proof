use std::{
    fs::{File, OpenOptions},
    io::Write,
    mem, slice,
};

use memmap::MmapOptions;
use plonky_block_proof_gen::types::AllRecursiveCircuits;
use tracing::{info, warn};

use super::circuit::CircuitConfig;

const PROVER_STATE_FILE_PREFIX: &str = "./prover_state";

#[inline]
fn disk_path(circuit_config: &CircuitConfig) -> String {
    format!(
        "{}_{}",
        PROVER_STATE_FILE_PREFIX,
        circuit_config.get_configuration_digest()
    )
}

pub fn from_disk(circuit_config: &CircuitConfig) -> Option<&'static AllRecursiveCircuits> {
    let path = disk_path(circuit_config);
    let file = File::open(&path).ok()?;
    info!("found prover state at {path}");
    info!("memory mapping state...");
    let mmap = unsafe { MmapOptions::new().map(&file) };
    if let Err(e) = mmap {
        warn!("failed to memory map prover state, {e:?}");
        return None;
    }
    let mmap = mmap.unwrap();

    unsafe {
        assert!(mmap.len() == mem::size_of::<AllRecursiveCircuits>());
        let state = &*(mmap.as_ptr() as *const AllRecursiveCircuits);
        Some(state)
    }
}

pub fn to_disk(circuits: &AllRecursiveCircuits, circuit_config: &CircuitConfig) {
    let file = OpenOptions::new()
        .write(true)
        .create(true)
        .open(disk_path(circuit_config));

    let mut file = match file {
        Ok(file) => file,
        Err(e) => {
            warn!("failed to create prover state file, {e:?}");
            return;
        }
    };

    unsafe {
        let bytes = slice::from_raw_parts(
            circuits as *const _ as *const u8,
            mem::size_of_val(circuits),
        );

        if let Err(e) = file.write_all(bytes) {
            warn!("failed to write prover state file, {e:?}");
        }
    }
}
