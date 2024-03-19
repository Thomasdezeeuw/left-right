use std::future::Future;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};
use std::task::{self, Poll};
use std::{panic, thread};

use left_right::operation::{Operation, OverwriteOperation};

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
fn read_guard_map() {
    let (_, handle) = left_right::new_cloned::<_, Vec<TestOperation>>(String::from("Hello"));
    let reader = handle.into_reader();

    unsafe { need_bytes(reader.read().map(|s| s.as_bytes()).deref()) };
    fn need_bytes(b: &[u8]) {
        assert_eq!(b, b"Hello");
    }
}

#[test]
fn read_guard_map_panic() {
    let (_, handle) = left_right::new_cloned::<_, Vec<TestOperation>>(String::from("Hello"));
    let reader = handle.into_reader();

    match panic::catch_unwind(|| unsafe { reader.read().map(|_| -> &str { panic!("oops") }) }) {
        Ok(_) => panic!("unexpected Ok"),
        Err(_) => { /* Expected. */ }
    }

    // The read should still be usable.
    assert_eq!(unsafe { reader.read().deref() }, "Hello");
}

#[test]
fn writer_apply_does_not_apply_to_reader_copy() {
    let (mut writer, handle) = left_right::new_from_default::<String, Vec<_>>();
    let reader = handle.into_reader();

    writer.apply(TestOperation::Append("test"));
    assert_eq!(unsafe { reader.read().deref() }, "");
}

#[test]
fn writer_apply_to_reader_copy_does_not_apply_to_writer_copy() {
    let (mut writer, handle) = left_right::new_cloned::<_, Vec<_>>(String::new());
    let reader = handle.into_reader();

    unsafe { writer.apply_to_reader_copy(TestOperation::Append("test")) };
    assert_eq!(writer.deref(), "");
    assert_eq!(reader.clone_value(), "");
}

#[test]
fn writer_blocking_flush_shows_changes_to_reader_copy() {
    let (mut writer, handle) =
        unsafe { left_right::new::<_, Vec<_>>(String::new(), String::new()) };
    let reader = handle.into_reader();

    writer.apply(TestOperation::Append("test"));
    writer.blocking_flush();
    assert_eq!(unsafe { reader.read().deref() }, "test");
}

#[test]
fn writer_blocking_flush_shows_changes_to_reader_copy_on_different_thread() {
    let (mut writer, handle) =
        unsafe { left_right::new::<_, Vec<_>>(String::new(), String::new()) };

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

#[test]
fn writer_flush_shows_changes_to_reader_copy() {
    let (mut writer, handle) =
        unsafe { left_right::new::<_, Vec<_>>(String::new(), String::new()) };
    let reader = handle.into_reader();

    writer.apply(TestOperation::Append("test"));

    let mut future = Box::pin(writer.flush());
    let (waker, wake_count) = new_count_waker();
    let mut ctx = task::Context::from_waker(&waker);
    assert_eq!(future.as_mut().poll(&mut ctx), Poll::Ready(()));

    assert_eq!(unsafe { reader.read().deref() }, "test");

    assert_eq!(wake_count, 0);
}

#[test]
fn writer_flush_shows_changes_to_reader_copy_on_different_thread() {
    let (mut writer, handle) =
        unsafe { left_right::new::<_, Vec<_>>(String::new(), String::new()) };

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

    let mut future = Box::pin(writer.flush());
    let (waker, wake_count) = new_count_waker();
    let mut ctx = task::Context::from_waker(&waker);
    loop {
        match future.as_mut().poll(&mut ctx) {
            Poll::Ready(()) => break,
            Poll::Pending => continue,
        }
    }
    drop(future);
    barrier.wait(); // Stage 3.
    assert_eq!(writer.deref(), "test");

    handle.join().unwrap();
    assert!(wake_count == 0 || wake_count == 1);
}

#[test]
fn writer_flush_future_dropped() {
    let (mut writer, handle) =
        unsafe { left_right::new::<_, Vec<_>>(String::new(), String::new()) };

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

    // Not polling the future, just dropping it.
    let future = writer.flush();
    drop(future);

    barrier.wait(); // Stage 3.
    assert_eq!(writer.deref(), "test");

    handle.join().unwrap();
}

#[test]
fn writer_flush_future_polled_many_times() {
    let (mut writer, handle) =
        unsafe { left_right::new::<_, Vec<_>>(String::new(), String::new()) };
    let reader = handle.into_reader();

    let read_guard = unsafe { reader.read() };

    writer.apply(TestOperation::Append("test"));

    let mut future = Box::pin(writer.flush());
    let (waker, wake_count) = new_count_waker();
    let mut ctx = task::Context::from_waker(&waker);
    for _ in 0..10 {
        assert_eq!(future.as_mut().poll(&mut ctx), Poll::Pending);
    }

    drop(read_guard);
    assert_eq!(future.as_mut().poll(&mut ctx), Poll::Ready(()));

    assert_eq!(unsafe { reader.read().deref() }, "test");
    drop(future);
    assert_eq!(unsafe { reader.read().deref() }, writer.deref());

    assert_eq!(wake_count, 1);
}

#[test]
fn writer_flush_future_polled_after_completion() {
    let (mut writer, handle) =
        unsafe { left_right::new::<_, Vec<_>>(String::new(), String::new()) };
    let reader = handle.into_reader();

    writer.apply(TestOperation::Append("test"));

    let mut future = Box::pin(writer.flush());
    let (waker, wake_count) = new_count_waker();
    let mut ctx = task::Context::from_waker(&waker);
    for _ in 0..10 {
        assert_eq!(future.as_mut().poll(&mut ctx), Poll::Ready(()));
    }

    assert_eq!(unsafe { reader.read().deref() }, "test");
    drop(future);
    assert_eq!(unsafe { reader.read().deref() }, writer.deref());

    assert_eq!(wake_count, 0);
}

#[test]
fn overwrite_operation_works() {
    let (mut writer, handle) = unsafe { left_right::new::<_, Vec<_>>("", "") };
    let reader = handle.into_reader();

    writer.apply(OverwriteOperation::new("test"));
    writer.blocking_flush();
    assert_eq!(unsafe { *reader.read().deref() }, "test");
}

fn new_count_waker() -> (task::Waker, AwokenCount) {
    let inner = Arc::new(WakerInner {
        count: AtomicUsize::new(0),
    });
    (task::Waker::from(inner.clone()), AwokenCount { inner })
}

#[derive(Debug)]
pub struct AwokenCount {
    inner: Arc<WakerInner>,
}

impl PartialEq<usize> for AwokenCount {
    fn eq(&self, other: &usize) -> bool {
        self.inner.count.load(Ordering::SeqCst) == *other
    }
}

#[derive(Debug)]
struct WakerInner {
    count: AtomicUsize,
}

impl task::Wake for WakerInner {
    fn wake(self: Arc<Self>) {
        WakerInner::wake_by_ref(&self)
    }

    fn wake_by_ref(self: &Arc<Self>) {
        let _ = self.count.fetch_add(1, Ordering::SeqCst);
    }
}
