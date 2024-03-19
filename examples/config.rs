use std::collections::HashMap;
use std::sync::Arc;

use left_right::operation::OverwriteOperation;

fn main() {
    // For the initial configuration we'll pretend it's empty.
    let initial_config = HashMap::new();
    // Wrap the configuration in an `Arc` so it can be cheaply cloned (it's read
    // only any way).
    let initial_config = Arc::new(initial_config);

    // Create a new left-right data structure from the configuration.
    let (mut writer, handle) =
        left_right::new_cloned::<_, Option<OverwriteOperation<_>>>(initial_config);

    // Do something useful...
    let reader = handle.into_reader();
    let config = reader.clone_value();
    println!("intial config: {config:?}");

    // Then to reload the configuration, for example after receiving a process
    // signal.
    let new_config = read_config();
    writer.apply(OverwriteOperation::new(Arc::new(new_config)));
    writer.blocking_flush();

    // Now the updated configuration can be read.
    let config = reader.clone_value();
    println!("new config: {config:?}");
}

/// Fake reading of the configuration file. Just for demostration purposes, not
/// very interesting (or efficient).
fn read_config() -> HashMap<String, String> {
    let mut config = HashMap::new();
    config.insert("address".to_owned(), "127.0.0.1:8080".to_owned());
    config.insert("message".to_owned(), "Hello, world!".to_owned());
    config
}
