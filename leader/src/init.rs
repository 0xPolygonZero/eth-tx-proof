use tracing_subscriber::{prelude::*, util::SubscriberInitExt, EnvFilter};
pub(crate) fn tracing() {
    tracing_subscriber::Registry::default()
        .with(
            tracing_subscriber::fmt::layer()
                .without_time()
                .with_ansi(false)
                .with_filter(EnvFilter::from_default_env()),
        )
        .init();
}
