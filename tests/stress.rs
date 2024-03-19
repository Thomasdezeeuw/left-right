use std::ops::Deref;
use std::sync::{Arc, Barrier};
use std::thread;

use left_right::Operation;

/// Number of read threads used.
const READ_THREADS: usize = 10;
/// Number of writes.
#[cfg(not(miri))]
const WRITES: usize = 100_000;
#[cfg(miri)]
const WRITES: usize = 500;

struct TestOperation;

unsafe impl Operation<usize> for TestOperation {
    fn apply(&self, target: &mut usize) {
        *target += 1;
    }
}

#[test]
fn stress_test() {
    let (mut writer, handle) = unsafe { left_right::new::<_, Vec<_>>(0, 0) };

    let barrier = Arc::new(Barrier::new(READ_THREADS + 1));
    let handles: Vec<_> = (0..READ_THREADS)
        .into_iter()
        .map(|_| {
            let handle = handle.clone();
            let barrier = barrier.clone();
            thread::spawn(move || {
                let reader = handle.into_reader();
                // Make sure the epoch is allocated for this thread.
                drop(unsafe { reader.read() });

                barrier.wait();

                let mut last_read = 0;
                while last_read < WRITES {
                    let read_guard = unsafe { reader.read() };
                    let current = read_guard.deref().clone();
                    assert!(current >= last_read);
                    last_read = current;
                }
            })
        })
        .collect();
    drop(handle);

    // Wait for the reader threads to start.
    barrier.wait();

    for _ in 0..WRITES {
        writer.apply(TestOperation);
        writer.blocking_flush();
    }

    handles.into_iter().for_each(|h| h.join().unwrap());
}
