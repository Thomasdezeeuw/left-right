use left_right::hashmap;

#[test]
fn reserve() {
    let (mut writer, handle) = hashmap::with_capacity::<&str, &str>(8);
    let reader = handle.into_reader();
    assert!(writer.capacity() >= 8);
    assert!(reader.capacity() >= 8);
    assert!(reader.is_empty());
    assert!(reader.len() == 0);

    writer.reserve(16);
    writer.blocking_flush();
    assert!(writer.capacity() >= 8);
    assert!(reader.capacity() >= 8);
}

#[test]
fn shrink() {
    let (mut writer, handle) = hashmap::with_capacity::<&str, &str>(16);
    let reader = handle.into_reader();
    assert!(writer.capacity() >= 16);
    assert!(reader.capacity() >= 16);

    writer.shrink_to(8);
    writer.blocking_flush();
    assert!(writer.capacity() < 16);
    assert!(reader.capacity() < 16);

    writer.shrink_to_fit();
    writer.blocking_flush();
    assert!(writer.capacity() == 0);
    assert!(reader.capacity() == 0);
}

#[test]
fn insert() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    assert!(reader.is_empty());
    assert!(!writer.is_empty());

    writer.blocking_flush();
    assert!(!writer.is_empty());
    assert_eq!(writer.get("1").copied(), Some("Hello"));
    assert!(!reader.is_empty());
    assert_eq!(reader.get_cloned("1"), Some("Hello"));
}

#[test]
fn remove() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    assert_eq!(writer.remove("1"), Some("Hello"));
    assert_eq!(writer.remove_entry("2"), Some(("2", "World")));

    assert!(!reader.is_empty());
    assert!(writer.is_empty());

    writer.blocking_flush();
    assert!(writer.is_empty());
    assert!(reader.is_empty());
}

#[test]
fn drain() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    for (key, value) in writer.drain() {
        match key {
            "1" => assert_eq!(value, "Hello"),
            "2" => assert_eq!(value, "World"),
            key => panic!("unexpected key-value pair: {key} => {value}"),
        }
    }

    assert!(!reader.is_empty());
    assert!(writer.is_empty());

    writer.blocking_flush();
    assert!(writer.is_empty());
    assert!(reader.is_empty());
}

#[test]
fn clear() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    writer.clear();

    assert!(!reader.is_empty());
    assert!(writer.is_empty());

    writer.blocking_flush();
    assert!(writer.is_empty());
    assert!(reader.is_empty());
}

#[test]
fn keys_cloned() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    let mut keys = reader.keys_cloned();
    keys.sort();
    assert_eq!(keys, ["1", "2"]);
}

#[test]
fn values_cloned() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    let mut values = reader.values_cloned();
    values.sort();
    assert_eq!(values, ["Hello", "World"]);
}

#[test]
fn key_values_cloned() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    let mut key_values = reader.key_values_cloned();
    key_values.sort();
    assert_eq!(key_values, [("1", "Hello"), ("2", "World")]);
}

#[test]
fn clone_hashmap() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    let clone = reader.clone_hashmap();
    assert_eq!(clone.len(), 2);
    assert_eq!(clone.get("1").copied(), Some("Hello"));
    assert_eq!(clone.get("2").copied(), Some("World"));
}

#[test]
fn get_key_value_cloned() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    assert_eq!(reader.get_key_value_cloned("1"), Some(("1", "Hello")));
    assert_eq!(reader.get_key_value_cloned("2"), Some(("2", "World")));
}

#[test]
fn contains_key() {
    let (mut writer, handle) = hashmap::new::<&str, &str>();
    let reader = handle.into_reader();
    assert!(reader.is_empty());

    writer.insert("1", "Hello");
    writer.insert("2", "World");
    writer.blocking_flush();

    assert!(reader.contains_key("1"));
    assert!(reader.contains_key("2"));
    assert!(!reader.contains_key("3"));
}
