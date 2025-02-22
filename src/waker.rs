//! [`Waker`].

use std::mem::ManuallyDrop;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::{ptr, task, thread};

/// Waker that can either be a [`task::Waker`] or a [`thread::Thread::unpark`]
/// based waker.
pub(super) struct Waker {
    /// The `data` and `vtable` field somewhat mimic the `task::RawWaker`, in
    /// fact it could be the exact fields to a `task::RawWaker`. With these two
    /// fields we support two kinds of wakers:
    /// 1. Thread based wakers using [`thread::Thread::unpark`]
    /// 2. `task::Waker` to support futures.
    ///
    /// # Invariants
    ///
    /// If `data` is not null `vtable` must be set.
    ///
    /// # Thread based Waker
    ///
    /// `vtable` is set to `THREAD_VTABLE`, but it is not an actual vtable.
    /// `data` is a transmuted [`thread::Thread`] (which is a pointer itself).
    ///
    /// # `task::Waker` based Waker
    ///
    /// `vtable` is set to a valid `&'static RawWakerVTable`, safe to pass to
    /// `task::RawWaker::new`. `data` is the data passed to the same
    /// `task::RawWaker::new` call.
    ///
    /// # Empty Waker
    ///
    /// If `data` is empty it means no waker is set. Note that this also means
    /// `vtable` must be empty. Also see the write and reader ordering below.
    ///
    /// # Write Order
    ///
    /// To support the invariants above the `vtable` must always be written
    /// first, then the `data` field. When writing the waker must currently be
    /// empty, i.e. `wake` or `clear` must have been caller previously.
    ///
    /// # Read Order
    ///
    /// To support the invariants above the `data` field must always be read
    /// before the `vtable`. The `vtable` field will only be valid if the `data`
    /// field is not null.
    data: AtomicPtr<()>,
    vtable: AtomicPtr<()>,
}

/// Fake vtable data for [`Waker`].
const THREAD_VTABLE: *mut () = 1 as *mut ();

impl Waker {
    /// Create a new `Waker`.
    pub(super) const fn new() -> Waker {
        Waker {
            data: AtomicPtr::new(ptr::null_mut()),
            vtable: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Set the waker to use a `thread` based waker.
    pub(super) fn set_thread(&self, thread: thread::Thread) {
        let data = thread.into_raw();
        unsafe { self.set_raw(data.cast_mut(), THREAD_VTABLE) };
    }

    /// Set the waker to use a `task_waker` based waker.
    pub(super) fn set_task_waker(&self, task_waker: task::Waker) {
        let task_waker = ManuallyDrop::new(task_waker);
        let data = task_waker.data();
        let vtable = task_waker.vtable();
        unsafe { self.set_raw(data as *mut (), vtable as *const _ as *const () as *mut ()) };
    }

    /// # Safety
    ///
    /// Caller must ensure `data` and `vtable` are correct according to the
    /// `Waker.data` and `Waker.vtable` docs.
    unsafe fn set_raw(&self, data: *mut (), vtable: *mut ()) {
        // Spurious thread wake-ups can happen and a `Future` should always be
        // pollable. So, we need to ensure the waker is in a clear state before
        // attempt to set it again.
        self.clear();

        // The call to `clear` above should have clear the `Waker`. However
        // `Waker::clear` only checks the `data` field and assumes that if the
        // `data` field is null, then so is the `vtable` field. But this is not
        // entirely true. It could be that another threads read `data`, but
        // hasn't had the change yet to read `vtable`, meaning it's not null.
        //
        // If we would use a `store` here the other thread would read the new
        // `vtable` and use that (incorrectly) with the old data. So, we need
        // this `compare_exchange` loop to ensure we're not overwriting a not
        // null value.
        //
        // Our thread            | Other thread
        // `set_raw`             | `wake`
        // `clear`               | read `data` -> data A
        // read `data` -> null   | swap `data` -> data A
        // store data B `vtable` | read `vtable` -> data B
        //                       | calls waker with `data` A , `vtable` B -> error.
        loop {
            match self.vtable.compare_exchange_weak(
                ptr::null_mut(),
                vtable,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => std::hint::spin_loop(),
            }
        }
        debug_assert!(self.data.load(Ordering::Relaxed).is_null());
        self.data.store(data, Ordering::SeqCst);
    }

    /// Wake the waker, if set.
    pub(super) fn wake(&self) {
        if self.data.load(Ordering::Relaxed).is_null() {
            // No data set, means no waker set.
            return;
        }

        let data = self.data.swap(ptr::null_mut(), Ordering::SeqCst);
        if !data.is_null() {
            let vtable = self.vtable.swap(ptr::null_mut(), Ordering::SeqCst);
            match vtable {
                THREAD_VTABLE => unsafe { thread::Thread::from_raw(data).unpark() },
                vtable => unsafe {
                    // It should not be possible for the `vtable` to be null.
                    // It's always set before the data is set and is always read
                    // after data is read.
                    debug_assert!(!vtable.is_null());

                    // SAFETY: per the docs on `Waker.vtable` it's either
                    // `THREAD_VTABLE` or a valid `RawWakerVTable` pointer.
                    let vtable: &'static task::RawWakerVTable = &*vtable.cast();
                    let raw = task::RawWaker::new(data, vtable);
                    // SAFETY: the caller gave us a `task::Waker` (in
                    // `set_task_waker`), assuming they followed the
                    // requirements we're also following them.
                    task::Waker::from_raw(raw).wake();
                },
            }
        }
    }

    /// Clears the waker, without waking it.
    pub(super) fn clear(&self) {
        // This follows the same pattern as [`Waker::wake`].

        if self.data.load(Ordering::Relaxed).is_null() {
            // No data set, means no waker set.
            return;
        }

        let data = self.data.swap(ptr::null_mut(), Ordering::SeqCst);
        if !data.is_null() {
            let vtable = self.vtable.swap(ptr::null_mut(), Ordering::SeqCst);
            match vtable {
                THREAD_VTABLE => unsafe { drop(thread::Thread::from_raw(data)) },
                vtable => unsafe {
                    debug_assert!(!vtable.is_null());

                    // SAFETY: see Waker::waker.
                    let vtable: &'static task::RawWakerVTable = &*vtable.cast();
                    let raw = task::RawWaker::new(data, vtable);
                    // SAFETY: see Waker::waker.
                    drop(task::Waker::from_raw(raw));
                },
            }
        }
    }
}
