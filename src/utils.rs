use flexi_logger::Logger;

pub fn init_env_logger() {
    let _ = Logger::try_with_env_or_str("plonky2::util::timing=info")
        .unwrap()
        .start();
}
