use std::ops::Deref;
use std::sync::{Arc, Barrier};
use std::thread;

use left_right::Operation;

enum TestOperation {
    Append(&'static str),
}

unsafe impl Operation<String> for TestOperation {
    fn apply(&self, target: &mut String) {
        match self {
            TestOperation::Append(str) => target.push_str(str),
        }
    }
}

#[test]
fn writer_apply_does_not_apply_to_reader_copy() {
    let (mut writer, handle) = unsafe { left_right::new(String::new(), String::new()) };
    let reader = handle.into_reader();

    writer.apply(TestOperation::Append("test"));
    assert_eq!(unsafe { reader.read().deref() }, "");
}

#[test]
fn writer_apply_to_reader_copy_does_not_apply_to_writer_copy() {
    let (mut writer, handle) = unsafe { left_right::new(String::new(), String::new()) };
    let reader = handle.into_reader();

    unsafe { writer.apply_to_reader_copy(TestOperation::Append("test")) };
    assert_eq!(writer.deref(), "");
    assert_eq!(unsafe { reader.read().deref() }, "");
}

#[test]
fn writer_flush_shows_changes_to_reader_copy() {
    let (mut writer, handle) = unsafe { left_right::new(String::new(), String::new()) };
    let reader = handle.into_reader();

    writer.apply(TestOperation::Append("test"));
    writer.blocking_flush();
    assert_eq!(unsafe { reader.read().deref() }, "test");
}

#[test]
fn write_flush_shows_changes_to_reader_copy() {
    let (mut writer, handle) = unsafe { left_right::new(String::new(), String::new()) };

    // Stages:
    // 1. Read guard held.
    // 2. Write made.
    // 3. Write flushed.
    let barrier = Arc::new(Barrier::new(2));

    let read_barrier = barrier.clone();
    let handle = thread::spawn(move || {
        let reader = handle.into_reader();

        let read_guard = unsafe { reader.read() };
        read_barrier.wait(); // Stage 1.

        read_barrier.wait(); // Stage 2.
        assert_eq!(read_guard.deref(), "");
        drop(read_guard);

        read_barrier.wait(); // Stage 3.
        assert_eq!(unsafe { reader.read().deref() }, "test");
    });

    barrier.wait(); // Stage 1.

    writer.apply(TestOperation::Append("test"));
    barrier.wait(); // Stage 2.

    writer.blocking_flush();
    barrier.wait(); // Stage 3.
    assert_eq!(writer.deref(), "test");

    handle.join().unwrap();
}
