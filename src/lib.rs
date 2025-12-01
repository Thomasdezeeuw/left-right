//! Concurrent left-right data structures.

#![feature(thread_id_value, thread_raw)]

use std::future::Future;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::num::NonZeroU64;
use std::ops::Deref;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{self, Poll};

pub mod operation;
pub use operation::{Log, Operation};

pub mod hashmap;

mod waker;

/// Create a new left-right data structure.
///
/// # Safety
///
/// `left` and `right` **must** be equal.
pub unsafe fn new<T, L: Log<T>>(left: T, right: T) -> (Writer<T, L>, Handle<T>) {
    let shared = unsafe { Shared::new(left, right) };
    (
        Writer {
            shared: shared.clone(),
            last_seen_epochs: Vec::new(),
            log: L::new(),
        },
        Handle { shared },
    )
}

/// Create a new left-right data structure from a default value.
///
/// # Safety
///
/// This function is safe based on the assumption that the [`Default`]
/// implementation for `T` always returns the same value. If this is not the
/// case the left and right copies will be out of sync.
pub fn new_from_default<T: Default, L: Log<T>>() -> (Writer<T, L>, Handle<T>) {
    unsafe { new(T::default(), T::default()) }
}

/// Create a new left-right data structure by cloning `value`.
///
/// # Safety
///
/// This function is safe based on the assumption that the [`Clone`]
/// implementation for `T` returns the same value as `value`. If this is not the
/// case the left and right copies will be out of sync.
pub fn new_cloned<T: Clone, L: Log<T>>(value: T) -> (Writer<T, L>, Handle<T>) {
    unsafe { new(value.clone(), value) }
}

/// Write access to the left-right data structure.
#[derive(Debug)]
pub struct Writer<T, L> {
    shared: Pin<Arc<Shared<T>>>,
    last_seen_epochs: Vec<usize>,
    log: L,
}

impl<T, L> Writer<T, L>
where
    L: Log<T>,
{
    /// Apply `operation` to the data structure.
    ///
    /// # Notes
    ///
    /// The `operation` will only be applied to the writer's copy of the data
    /// structure, **not** the readers' copy. For the change to take affect call
    /// [`Writer::flush`].
    pub fn apply(&mut self, operation: L::Operation) {
        operation.apply(self.value_mut());
        self.log.push(operation);
    }

    /// Unlike [`Writer::apply`] this only applies `operation` to the reader's
    /// copy, not to the writers copy.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `operation` (equivalent) is already applied
    /// to the writer's copy, otherwise the two would go out of sync.
    pub unsafe fn apply_to_reader_copy(&mut self, operation: L::Operation) {
        self.log.push(operation);
    }

    /// Flush all previously [applied] operations so that the readers can see
    /// the changes made.
    ///
    /// [applied]: Writer::apply
    ///
    /// # Notes
    ///
    /// This is a no-op if no writer operations were applied.
    pub fn blocking_flush(&mut self) {
        if self.log.is_empty() {
            return;
        }

        // Switch the writer and reader copies and block until all readers are
        // using the new copy.
        // SAFETY: we're the `Writer`.
        unsafe {
            self.shared
                .as_ref()
                .switch_reading(&mut self.last_seen_epochs)
        };

        // Next apply all operations we applied to the old writer copy to the
        // new copy to ensure both are in sync again.
        // SAFETY: we're the `Writer`.
        let value = unsafe { self.shared.as_ref().writer_access_mut() };
        self.log.apply_and_clear(&mut *value);
    }

    /// Flush all previously [applied] operations so that the readers can see
    /// the changes made.
    ///
    /// [applied]: Writer::apply
    ///
    /// # Notes
    ///
    /// If the returned [`Future`] is dropped before it is polled to completion
    /// it will block until the writes are flushed (effectively calling
    /// [`Writer::blocking_flush`]), otherwise it would leave `Writer` in an
    /// invalid state.
    ///
    /// # Safety
    ///
    /// If the returned [`Flush`] `Future` is not polled to completion **and**
    /// it is leaked `Writer` will be an invalid state not safe to use any more.
    pub fn flush<'a>(&'a mut self) -> Flush<'a, T, L> {
        // This follows the same pattern as [`Writer::blocking_flush`].

        let shared = self.shared.as_ref();
        unsafe { shared.switch_reading_pointers() };
        shared.fill_epochs(&mut self.last_seen_epochs);

        Flush {
            writer: self,
            flushed: false,
        }
        // Continued in `Flush::poll` and/or `Flush::drop`.
    }

    /// Get mutable access to the value `T`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that any changes made to the value MUST be
    /// replicated to the reader's copy using [`Writer::apply_to_reader_copy`].
    pub unsafe fn access_mut(&mut self) -> &mut T {
        self.value_mut()
    }

    fn value_mut(&mut self) -> &mut T {
        // SAFETY: we're the `Writer`.
        unsafe { self.shared.as_ref().writer_access_mut() }
    }
}

impl<T, L> Deref for Writer<T, L> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: we're the `Writer`.
        unsafe { self.shared.as_ref().writer_access() }
    }
}

/// [`Future`] behind [`Writer::flush`].
#[must_use = "futures do nothing unless you `.await` or poll them"]
#[derive(Debug)]
pub struct Flush<'a, T, L: Log<T>> {
    writer: &'a mut Writer<T, L>,
    flushed: bool,
}

impl<'a, T, L: Log<T>> Flush<'a, T, L> {
    /// Apply all operations to the current writer copy (the old reader copy).
    ///
    /// # Safety
    ///
    /// Caller must ensure that all readers have switched to the new copy, by
    /// calling [`Shared::all_readers_switched`].
    unsafe fn apply_operations(&mut self) {
        // SAFETY: we're the `Writer`.
        let value = unsafe { self.writer.shared.as_ref().writer_access_mut() };
        self.writer.log.apply_and_clear(&mut *value);
        self.flushed = true;
    }
}

impl<'a, T, L: Log<T>> Future for Flush<'a, T, L> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, ctx: &mut task::Context<'_>) -> Poll<()> {
        // This follows the same pattern as [`Writer::blocking_flush`].

        let this = Pin::into_inner(self);
        let shared = this.writer.shared.as_ref();
        if shared.all_readers_switched(&mut this.writer.last_seen_epochs) {
            unsafe { this.apply_operations() };
            return Poll::Ready(());
        }

        // Make sure we get polled again.
        shared.set_writer_task_waker(ctx.waker().clone());

        if shared.all_readers_switched(&mut this.writer.last_seen_epochs) {
            shared.clear_writer_waker();
            unsafe { this.apply_operations() };
            return Poll::Ready(());
        }

        Poll::Pending
    }
}

impl<'a, T, L: Log<T>> Drop for Flush<'a, T, L> {
    fn drop(&mut self) {
        if !self.flushed {
            let epochs = &mut self.writer.last_seen_epochs;
            let shared = self.writer.shared.as_ref();
            shared.block_until_all_readers_switched(epochs);
            unsafe { self.apply_operations() };
        }
    }
}

/// A handle to the left-right data structure that provides no access.
///
/// With this handle you can do three things:
///  * Move it to another thread ([`Reader`]s can't be moved across threads).
///  * Convert it into a [`Reader`].
///  * Cheaply [`clone`] it.
///
/// [`clone`]: Clone
#[derive(Debug)]
pub struct Handle<T> {
    shared: Pin<Arc<Shared<T>>>,
}

impl<T> Handle<T> {
    /// Turn this `Handle` into a `Reader`.
    pub fn into_reader(self) -> Reader<T> {
        let epoch_index = self.shared.as_ref().epoch_index();
        Reader {
            handle: self,
            epoch_index,
            _not_send: PhantomData,
        }
    }
}

impl<T> Clone for Handle<T> {
    fn clone(&self) -> Handle<T> {
        Handle {
            shared: self.shared.clone(),
        }
    }
}

/// Read access to the left-right data structure.
///
/// A `Reader` is always bound to a thread and is thus not [`Send`], to move a
/// reader across first convert into a [`Handle`].
#[derive(Debug)]
pub struct Reader<T> {
    handle: Handle<T>,
    /// Index into the epochs vector.
    epoch_index: NonZeroU64,
    /// The `Reader` must be `!Send` as the epoch index is based on the thread
    /// id, which will change if we change threads.
    _not_send: PhantomData<*const ()>,
}

impl<T> Reader<T> {
    /// Get read access to the data structure.
    ///
    /// While the returned `ReadGuard` lives it will block the flushing of all
    /// writes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that no two `ReadGuard`s are alive on the same
    /// thread. This means that no other method may be called on **any**
    /// `Reader` (not just this one) while `ReadGuard` is alive.
    pub unsafe fn read<'a>(&'a self) -> ReadGuard<'a, T> {
        let shared = self.handle.shared.as_ref();
        ReadGuard {
            value: shared.mark_reading(self.epoch_index),
            status: shared.status(),
            epoch_index: self.epoch_index,
            _not_send: PhantomData,
        }
    }

    /// Returns a clone of the value.
    pub fn clone_value(&self) -> T
    where
        T: Clone,
    {
        unsafe { self.read().deref().clone() }
    }

    /// Returns the underlying `Handle` from this `Reader`.
    pub fn as_handle(&self) -> &Handle<T> {
        &self.handle
    }

    /// Convert this `Reader` into a `Handle` so it can be moved across threads.
    pub fn into_handle(self) -> Handle<T> {
        self.handle
    }
}

impl<T> From<Handle<T>> for Reader<T> {
    fn from(handle: Handle<T>) -> Reader<T> {
        handle.into_reader()
    }
}

impl<T> Clone for Reader<T> {
    fn clone(&self) -> Reader<T> {
        Reader {
            handle: self.handle.clone(),
            epoch_index: self.epoch_index,
            _not_send: PhantomData,
        }
    }

    fn clone_from(&mut self, source: &Reader<T>) {
        let Reader {
            handle,
            epoch_index,
            _not_send,
        } = self;
        // NOTE: don't need to copy `epoch_index` as it should already be the
        // same (can't move `Reader` across thread bounds after all).
        debug_assert!(*epoch_index == source.epoch_index);
        handle.clone_from(&source.handle);
    }
}

/// Similar to a mutex guard this protects the data structure so that the read
/// access is properly synchronised with possible concurrent writes.
#[derive(Debug)]
pub struct ReadGuard<'a, T: ?Sized> {
    value: &'a T,
    status: Pin<&'a Status>,
    epoch_index: NonZeroU64,
    /// The `ReaderGuard` must be `!Send` as the epoch index is based on the
    /// thread id, which will change if we change threads.
    _not_send: PhantomData<*const ()>,
}

impl<'a, T: ?Sized> ReadGuard<'a, T> {
    /// Map the value `T` to `U`.
    pub fn map<F, U>(self, map: F) -> ReadGuard<'a, U>
    where
        F: FnOnce(&'a T) -> &'a U,
        U: ?Sized,
    {
        // NOTE: we need to call the `map` function before using `ManuallyDrop`
        // below in case of panics.
        let new_value = map(self.value);
        // Don't drop the old guard as that will change our epoch.
        let guard = ManuallyDrop::new(self);
        ReadGuard {
            value: new_value,
            status: guard.status,
            epoch_index: guard.epoch_index,
            _not_send: PhantomData,
        }
    }
}

impl<'a, T: ?Sized> Deref for ReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized> Drop for ReadGuard<'a, T> {
    fn drop(&mut self) {
        self.status.mark_done_reading(self.epoch_index);
    }
}

mod shared {
    //! Module to make the fields in [`Shared`] private.

    use std::cell::UnsafeCell;
    use std::iter::zip;
    use std::num::NonZeroU64;
    use std::panic::RefUnwindSafe;
    use std::pin::Pin;
    use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
    use std::sync::{Arc, RwLock};
    use std::{ptr, task, thread};

    use super::waker::Waker;

    /// Data shared between the readers and writer.
    ///
    /// # Safety
    ///
    /// Must always be pinned in memory!
    #[derive(Debug)]
    pub(super) struct Shared<T> {
        /// Pointer to either `left` or `right`.
        ///
        /// # Safety
        ///
        /// This must always point to either `left` or `right` and must be valid
        /// for at least as long as `Shared` lives.
        read: AtomicPtr<T>,
        /// Status
        status: Status,
        /// Is `read` pointing to `left` or `right?
        /// Maybe only be accessed by the writer.
        reading: UnsafeCell<Reading>,
        /// Left copy.
        /// Maybe only be accessed by the writer **iff** `read` is currently
        /// pointing to `right`.
        left: UnsafeCell<T>,
        /// Right copy.
        /// Maybe only be accessed by the writer **iff** `read` is currently
        /// pointing to `left`.
        right: UnsafeCell<T>,
    }

    /// Status of [`Shared`].
    ///
    /// This is a separate type so it can be used in `ReadGuard` without a type,
    /// allowing `ReadGuard::map` to exist.
    #[derive(Debug)]
    pub(super) struct Status {
        /// Epochs for the readers.
        read_epochs: RwLock<Vec<AtomicUsize>>,
        /// Waker for the writer.
        waker: Waker,
    }

    /// Are we writing to the left or right data structure?
    enum Reading {
        Left,
        Right,
    }

    impl<T> Shared<T> {
        /// # Safety
        ///
        /// `left` and `right` **must** be equal.
        pub(super) unsafe fn new(left: T, right: T) -> Pin<Arc<Shared<T>>> {
            let shared = Arc::pin(Shared {
                read: AtomicPtr::new(ptr::null_mut()), // NOTE: set below.
                status: Status {
                    read_epochs: RwLock::new(Vec::new()),
                    waker: Waker::new(),
                },
                reading: UnsafeCell::new(Reading::Left),
                left: UnsafeCell::new(left),
                right: UnsafeCell::new(right),
            });
            shared.read.store(shared.left.get(), Ordering::Relaxed);
            shared
        }

        /// Returns a pinned reference to `Status`.
        pub(super) fn status(self: Pin<&Self>) -> Pin<&Status> {
            unsafe { Pin::map_unchecked(self, |s| &s.status) }
        }

        /// Get read access to the `Writer`'s copy of data structure.
        ///
        /// # Safety
        ///
        /// Only the `Writer` is allowed to call this.
        pub(super) unsafe fn writer_access<'a>(self: Pin<&'a Self>) -> &'a T {
            // SAFETY: caller must ensure we're the writer.
            match &*self.reading.get() {
                Reading::Left => &*self.right.get(),
                Reading::Right => &*self.left.get(),
            }
        }

        /// Get write access to the `Writer`'s copy of data structure.
        ///
        /// # Safety
        ///
        /// Only the `Writer` is allowed to call this.
        pub(super) unsafe fn writer_access_mut<'a>(self: Pin<&'a Self>) -> &'a mut T {
            // SAFETY: caller must ensure we're the writer.
            match &*self.reading.get() {
                Reading::Left => &mut *self.right.get(),
                Reading::Right => &mut *self.left.get(),
            }
        }

        /// Set the writer's waker to `task_waker`.
        pub(super) fn set_writer_task_waker(self: Pin<&Self>, task_waker: task::Waker) {
            self.status.waker.set_task_waker(task_waker);
        }

        /// Clear the writer's waker.
        pub(super) fn clear_writer_waker(self: Pin<&Self>) {
            self.status.waker.clear();
        }

        /// Switch the pointer to the other copy.
        ///
        /// # Safety
        ///
        /// Only the `Writer` is allowed to call this.
        pub(super) unsafe fn switch_reading(self: Pin<&Self>, current_epochs: &mut Vec<usize>) {
            self.switch_reading_pointers();
            self.fill_epochs(current_epochs);

            // If one or more readers are currently accessing the writer's copy
            // (after the switch above) we have to wait for them to increase
            // their epoch, as that means they've stopped accessing the copy.
            // Note have that after that they can increase their epoch again,
            // but at that point they'll be accessing the new reader's copy (as
            // we switched above).
            self.block_until_all_readers_switched(current_epochs);
        }

        /// Switch the reader's pointer to the current writer's copy.
        ///
        /// # Safety
        ///
        /// **After this function returns the `Shared` object is in an invalid
        /// state**. The caller **must** ensure that all readers are reading
        /// from the new reader's copy before accessing the old reader's copy.
        ///
        /// Only the `Writer` is allowed to call this.
        pub(super) unsafe fn switch_reading_pointers(self: Pin<&Self>) {
            // SAFETY: caller must ensure we're the writer.
            let ptr = match &mut *self.reading.get() {
                reading @ Reading::Left => {
                    *reading = Reading::Right;
                    self.right.get()
                }
                reading @ Reading::Right => {
                    *reading = Reading::Left;
                    self.left.get()
                }
            };
            // Switch which copy the readers are accessing.
            self.read.store(ptr, Ordering::SeqCst);
            // NOTE: per the docs, the `Shared` object is not in an invalid
            // state.
        }

        /// Fills `epochs` with the values of `self.status.read_epochs`.
        pub(super) fn fill_epochs(self: Pin<&Self>, epochs: &mut Vec<usize>) {
            epochs.clear();
            epochs.extend(
                self.status
                    .read_epochs
                    .read()
                    .unwrap()
                    .iter()
                    .map(|epoch| epoch.load(Ordering::SeqCst)),
            );
        }

        /// Returns true if all readers have increased their epoch or were not
        /// in a reading state in `current_epochs`.
        ///
        /// # Notes
        ///
        /// This function set the state of the reader to 0 in `current_epochs`
        /// if the reader advanced it's epoch to prevent unnecessary loading of
        /// the reader's epoch.
        pub(super) fn all_readers_switched(self: Pin<&Self>, current_epochs: &mut [usize]) -> bool {
            // We check if the current epoch (`ce`) is in a not-accessing state
            // (`% 2 == 0`) or if the new epoch (`ne`) is in a different state
            // then previously recorded (`ce != ne`). Note we use `!=` instead
            // of `>` because the epoch can wrap around (after 2^63 reads).
            zip(
                current_epochs.iter_mut(),
                self.status.read_epochs.read().unwrap().iter(),
            )
            .all(|(ce, ne)| {
                // If we know the reader is not accessing the value we don't
                // have to load their epoch.
                if *ce % 2 == 0 {
                    return true;
                }

                if *ce != ne.load(Ordering::SeqCst) {
                    *ce = 0; // Short circuit in the next iteration.
                    true
                } else {
                    false
                }
            })
        }

        /// Block until `all_readers_switched` return true, by parking the
        /// thread.
        pub(super) fn block_until_all_readers_switched(
            self: Pin<&Self>,
            current_epochs: &mut [usize],
        ) {
            loop {
                if self.all_readers_switched(current_epochs) {
                    // No more readers are accessing the writer's copy, so we
                    // safely return ensuring that only the writer has access to
                    // this copy.
                    return;
                }

                // Mark ourselves as parked, this ensures that the readers will
                // unpark us.
                let thread = thread::current();
                self.status.waker.set_thread(thread);

                // Before we can park ourselves we have to check the readers
                // epochs again. This is to prevent a race between the last time
                // we checked the reader epochs and marked ourselves as parked.
                if self.all_readers_switched(current_epochs) {
                    self.status.waker.clear();
                    return;
                }

                thread::park();
            }
        }

        /// Returns the epoch index.
        pub(super) fn epoch_index(self: Pin<&Self>) -> NonZeroU64 {
            let index = thread::current().id().as_u64();
            let length_required = (index.get() + 1) as usize;
            if self.status.read_epochs.read().unwrap().len() < length_required {
                // Not enough epoch allocated, allocate them now, but first
                // check the epochs haven't changed in the time between
                // releasing the read lock and acquiring the write lock.
                let mut epochs = self.status.read_epochs.write().unwrap();
                if epochs.len() < length_required {
                    epochs.resize_with(length_required, || AtomicUsize::new(0));
                }
            }
            index
        }

        /// Mark thread with `epoch_index` as reading.
        pub(super) fn mark_reading<'a>(self: Pin<&'a Self>, epoch_index: NonZeroU64) -> &'a T {
            // SAFETY: `epoch_index` ensures the `read_epochs` vector is long
            // enough to make this index safe.
            let old_epoch = self.status.read_epochs.read().unwrap()[epoch_index.get() as usize]
                .fetch_add(1, Ordering::SeqCst);
            debug_assert!(
                old_epoch % 2 == 0,
                "holding two read guards on the same thread"
            );
            // SAFETY: safe based on the requirements on `Shared.read`.
            unsafe { &*self.read.load(Ordering::SeqCst) }
        }
    }

    impl Status {
        /// Mark thread with `epoch_index` as done reading.
        pub(super) fn mark_done_reading(self: Pin<&Self>, epoch_index: NonZeroU64) {
            // SAFETY: `epoch_index` ensures the `read_epochs` vector is long
            // enough to make this index safe.
            let old_epoch = self.read_epochs.read().unwrap()[epoch_index.get() as usize]
                .fetch_add(1, Ordering::SeqCst);
            debug_assert!(old_epoch % 2 == 1, "invalid epoch state");
            self.waker.wake()
        }
    }

    unsafe impl<T: Sync + Send> Sync for Shared<T> {}
    unsafe impl<T: Sync + Send> Send for Shared<T> {}

    impl<T: RefUnwindSafe> RefUnwindSafe for Shared<T> {}
}

use shared::{Shared, Status};
