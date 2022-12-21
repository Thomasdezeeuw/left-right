//! Concurrent left-right data structures.

#![feature(thread_id_value, waker_getters)]

use std::future::Future;
use std::marker::PhantomData;
use std::num::NonZeroU64;
use std::ops::Deref;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{self, Poll};

/// Create a new left-right data structure.
///
/// # Safety
///
/// `left` and `right` **must** be equal.
pub unsafe fn new<T, O>(left: T, right: T) -> (Writer<T, O>, Handle<T>) {
    let shared = unsafe { Shared::new(left, right) };
    (
        Writer {
            shared: shared.clone(),
            last_seen_epochs: Vec::new(),
            log: Vec::new(),
        },
        Handle { shared },
    )
}

/// Write access to the left-right data structure.
pub struct Writer<T, O> {
    shared: Pin<Arc<Shared<T>>>,
    last_seen_epochs: Vec<usize>,
    log: Vec<O>,
}

impl<T, O> Writer<T, O>
where
    O: Operation<T>,
{
    /// Apply `operation` to the data structure.
    ///
    /// # Notes
    ///
    /// The `operation` will only be applied to the writer's copy of the data
    /// structure, **not** the readers' copy. For the change to take affect call
    /// [`Writer::flush`].
    pub fn apply(&mut self, operation: O) {
        operation.apply(self.value_mut());
        self.log.push(operation);
    }

    /// Unlike [`Writer::apply`] this only applies `operation` to the reader's
    /// copy, not to the writers copy.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `operation` (equivalent) operation is
    /// already applied to the writer's copy, otherwise the two would go out of
    /// sync.
    pub unsafe fn apply_to_reader_copy(&mut self, operation: O) {
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
        // SAFETY: We're the `Writer`.
        let value = unsafe { self.shared.as_ref().writer_access_mut() };
        for operation in self.log.drain(..) {
            operation.apply_again(&mut *value);
        }
        self.log.clear();
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
    /// leaked `Writer` will be an invalid state not safe to use any more.
    pub fn flush<'a>(&'a mut self) -> Flush<'a, T, O> {
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
        // SAFETY: We're the `Writer`.
        unsafe { self.shared.as_ref().writer_access_mut() }
    }
}

impl<T, O> Deref for Writer<T, O> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: We're the `Writer`.
        unsafe { self.shared.as_ref().writer_access() }
    }
}

/// Operation to apply to a left-right data structure.
///
/// # Safety
///
/// The implementation of this trait must ensure that the correctness
/// instructions are followed.
pub unsafe trait Operation<T> {
    /// Apply operation to `target`.
    ///
    /// # Correctness
    ///
    /// The operation will be applied twice, once to both copies. Both times it
    /// **must** have the same result.
    ///
    /// # Examples
    ///
    /// The example below will consistently apply the same calculator operations
    /// to the state type of `usize`.
    ///
    /// ```
    /// use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};
    ///
    /// use left_right::Operation;
    ///
    /// enum Calculator {
    ///     Addition(usize),
    ///     Subtraction(usize),
    ///     Multiplication(usize),
    ///     Division(usize),
    /// }
    ///
    /// unsafe impl<T> Operation<T> for Calculator
    /// where
    ///     T: AddAssign<usize> + DivAssign<usize> + MulAssign<usize> + SubAssign<usize>,
    /// {
    ///     fn apply(&self, target: &mut T) {
    ///         use Calculator::*;
    ///         match self {
    ///             Addition(n) => target.add_assign(*n),
    ///             Subtraction(n) => target.sub_assign(*n),
    ///             Multiplication(n) => target.mul_assign(*n),
    ///             Division(n) => target.div_assign(*n),
    ///         }
    ///     }
    /// }
    /// ```
    fn apply(&self, target: &mut T);

    /// Same as [`Operation::apply`], but can take ownership of `self` to avoid
    /// things like cloning and allocation by simply moving the value into
    /// `target`.
    ///
    /// The default implementation simply calls `apply`.
    ///
    /// # Correctness
    ///
    /// This must do the same thing as `apply`, furthermore it may not be
    /// assumed this will be called at all.
    fn apply_again(self, target: &mut T)
    where
        Self: Sized,
    {
        self.apply(target);
    }
}

/// [`Future`] behind [`Writer::flush`].
pub struct Flush<'a, T, O: Operation<T>> {
    writer: &'a mut Writer<T, O>,
    flushed: bool,
}

impl<'a, T, O: Operation<T>> Flush<'a, T, O> {
    /// Apply all operations to the current writer copy (the old reader copy).
    ///
    /// # Safety
    ///
    /// Caller must ensure that all readers have switched to the new copy, by
    /// calling [`Shared::all_readers_switched`].
    unsafe fn apply_operations(&mut self) {
        // SAFETY: We're the `Writer`.
        let value = unsafe { self.writer.shared.as_ref().writer_access_mut() };
        for operation in self.writer.log.drain(..) {
            operation.apply_again(&mut *value);
        }
        self.writer.log.clear();
        self.flushed = true;
    }
}

impl<'a, T, O: Operation<T>> Future for Flush<'a, T, O> {
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
        shared.waker.set_task_waker(ctx.waker().clone());

        if shared.all_readers_switched(&mut this.writer.last_seen_epochs) {
            shared.waker.clear();
            unsafe { this.apply_operations() };
            return Poll::Ready(());
        }

        Poll::Pending
    }
}

impl<'a, T, O: Operation<T>> Drop for Flush<'a, T, O> {
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
    /// thread.
    pub unsafe fn read<'a>(&'a self) -> ReadGuard<'a, T> {
        let shared = self.handle.shared.as_ref();
        ReadGuard {
            value: shared.mark_reading(self.epoch_index),
            shared,
            epoch_index: self.epoch_index,
            _not_send: PhantomData,
        }
    }

    /// Create new a `Handle` from this `Reader` so it can be moved across
    /// threads.
    pub fn as_handle(&self) -> &Handle<T> {
        &self.handle
    }

    /// Convert this `Reader` into a `Handle` so it can be moved across threads.
    pub fn into_handle(self) -> Handle<T> {
        self.handle
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
        // NOTE: don't need to copy `epoch_index` as it should already be the
        // same (can't move `Reader` across thread bounds after all).
        debug_assert!(self.epoch_index == source.epoch_index);
        self.handle = source.handle.clone();
    }
}

/// Similar to a mutex guard this protects the data structure so that the read
/// access is properly synchronised with possible concurrent writes.
pub struct ReadGuard<'a, T> {
    value: &'a T,
    shared: Pin<&'a Shared<T>>,
    epoch_index: NonZeroU64,
    /// The `Reader` must be `!Send` as the epoch index is based on the thread
    /// id, which will change if we change threads.
    _not_send: PhantomData<*const ()>,
}

impl<'a, T> Deref for ReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T> Drop for ReadGuard<'a, T> {
    fn drop(&mut self) {
        self.shared.mark_done_reading(self.epoch_index);
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
    use std::{ptr, thread};

    use super::waker::Waker;

    /// Data shared between the readers and writer.
    ///
    /// # Safety
    ///
    /// Must always be pinned in memory!
    pub(super) struct Shared<T> {
        /// Pointer to either `left` or `right`.
        ///
        /// # Safety
        ///
        /// This must always point to either `left` or `right` and must be valid
        /// for at least as long as `Shared` lives.
        read: AtomicPtr<T>,
        /// Epochs for the readers.
        read_epochs: RwLock<Vec<AtomicUsize>>,
        /// Is `read` pointing to `left` or `right?
        /// Maybe only be accessed by the writer.
        reading: UnsafeCell<Reading>,
        /// Waker for the writer.
        pub(super) waker: Waker,
        /// Left copy.
        /// Maybe only be accessed by the writer **iff** `read` is currently
        /// pointing to `right`.
        left: UnsafeCell<T>,
        /// Right copy.
        /// Maybe only be accessed by the writer **iff** `read` is currently
        /// pointing to `left`.
        right: UnsafeCell<T>,
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
                read_epochs: RwLock::new(Vec::new()),
                reading: UnsafeCell::new(Reading::Left),
                waker: Waker::new(),
                left: UnsafeCell::new(left),
                right: UnsafeCell::new(right),
            });
            shared
                .read
                .store(&shared.left as *const _ as *mut _, Ordering::Relaxed);
            shared
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
                    &self.right
                }
                reading @ Reading::Right => {
                    *reading = Reading::Left;
                    &self.left
                }
            } as *const _ as *mut _;
            // Switch which copy the readers are accessing.
            self.read.store(ptr, Ordering::SeqCst);
            // NOTE: per the docs, the `Shared` object is not in an invalid
            // state.
        }

        /// Fills `epochs` with the values of `self.read_epochs`.
        pub(super) fn fill_epochs(self: Pin<&Self>, epochs: &mut Vec<usize>) {
            epochs.clear();
            epochs.extend(
                self.read_epochs
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
                self.read_epochs.read().unwrap().iter(),
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
                self.waker.set_thread(thread);

                // Before we can park ourselves we have to check the readers
                // epochs again. This is to prevent a race between the last time
                // we checked the reader epochs and marked ourselves as parked.
                if self.all_readers_switched(current_epochs) {
                    self.waker.clear();
                    return;
                }

                thread::park();
            }
        }

        /// Returns the epoch index.
        pub(super) fn epoch_index(self: Pin<&Self>) -> NonZeroU64 {
            let index = thread::current().id().as_u64();
            let length_required = (index.get() + 1) as usize;
            if self.read_epochs.read().unwrap().len() < length_required {
                // Not enough epoch allocated, allocate them now, but first
                // check the epochs haven't changed in the time between
                // releasing the read lock and acquiring the write lock.
                let mut epochs = self.read_epochs.write().unwrap();
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
            let old_epoch = self.read_epochs.read().unwrap()[epoch_index.get() as usize]
                .fetch_add(1, Ordering::SeqCst);
            debug_assert!(
                old_epoch % 2 == 0,
                "holding two read guards on the same thread"
            );
            // SAFETY: safe based on the requirements on `Shared.read`.
            unsafe { &*self.read.load(Ordering::SeqCst) }
        }

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

use shared::Shared;

mod waker {
    //! Module to make the fields in [`Waker`] private.

    use std::mem::ManuallyDrop;
    use std::sync::atomic::{AtomicPtr, Ordering};
    use std::{ptr, task, thread};

    /// Waker that can either be a [`task::Waker`] or a
    /// [`thread::Thread::unpark`] based waker.
    pub(super) struct Waker {
        /// The `data` and `vtable` field somewhat mimic the `task::RawWaker`,
        /// in fact it could be the exact fields to a `task::RawWaker`. With
        /// these two fields we support two kinds of wakers:
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
        /// `data` is a transmuted [`thread::Thread`] (which is a pointer
        /// itself).
        ///
        /// # `task::Waker` based Waker
        ///
        /// `vtable` is set to a valid `&'static RawWakerVTable`, safe to pass
        /// to `task::RawWaker::new`. `data` is the data passed to the same
        /// `task::RawWaker::new` call.
        ///
        /// # Empty Waker
        ///
        /// If `data` is empty it means no waker is set. Note that this also
        /// means `vtable` must be empty. Also see the write and reader ordering
        /// below.
        ///
        /// # Write Order
        ///
        /// To support the invariants above the `vtable` must always be written
        /// first, then the `data` field. When writing the waker must currently
        /// be empty, i.e. `wake` or `clear` must have been caller previously.
        ///
        /// # Read Order
        ///
        /// To support the invariants above the `data` field must always be read
        /// before the `vtable`. The `vtable` field will only be valid if the
        /// `data` field is not null.
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
            let data = thread_as_ptr(thread);
            unsafe { self.set_raw(data, THREAD_VTABLE) };
        }

        /// Set the waker to use a `task_waker` based waker.
        pub(super) fn set_task_waker(&self, task_waker: task::Waker) {
            let task_waker = ManuallyDrop::new(task_waker);
            let raw_waker = task_waker.as_raw();
            let data = raw_waker.data();
            let vtable = raw_waker.vtable();
            unsafe { self.set_raw(data as *mut (), vtable as *const _ as *const () as *mut ()) };
        }

        /// # Safety
        ///
        /// Caller must ensure `data` and `vtable` are correct according to the
        /// `Waker.data` and `Waker.vtable` docs.
        unsafe fn set_raw(&self, data: *mut (), vtable: *mut ()) {
            // Spurious thread wake-ups can happend and a `Future` should always
            // be pollable. So, we need to ensure the waker is in a clear state
            // before attempt to set it again.
            self.clear();

            // The call to `clear` above should have clear the `Waker`. However
            // `Waker::clear` only checks the `data` field and assumes that if
            // the `data` field is null, then so is the `vtable` field. But this
            // is not entirely true. It could be that another threads read
            // `data`, but hasn't had the change yet to read `vtable`, meaning
            // it's not null.
            //
            // If we would use a `store` here the other thread would read the
            // new `vtable` and use that (incorrectly) with the old data. So, we
            // need this `compare_exchange` loop to ensure we're not overwriting
            // a not null value.
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
                    THREAD_VTABLE => unsafe { ptr_as_thread(data).unpark() },
                    vtable => unsafe {
                        // It should not be possible for the `vtable` to be
                        // null. It's always set before the data is set and is
                        // always read after data is read.
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
                    THREAD_VTABLE => unsafe { drop(ptr_as_thread(data)) },
                    vtable => unsafe {
                        debug_assert!(!vtable.is_null());

                        // SAFETY: See Waker::waker.
                        let vtable: &'static task::RawWakerVTable = &*vtable.cast();
                        let raw = task::RawWaker::new(data, vtable);
                        // SAFETY: See Waker::waker.
                        drop(task::Waker::from_raw(raw));
                    },
                }
            }
        }
    }

    /// Returns `thread` as a pointer.
    fn thread_as_ptr(thread: thread::Thread) -> *mut () {
        // SAFETY: this is not safe.
        // However `Thread` under the hood is just a `Pin<Arc>`, which is just a
        // pointer, so it does work.
        unsafe { std::mem::transmute(thread) }
    }

    /// Reverse of [`thread_as_ptr`].
    unsafe fn ptr_as_thread(ptr: *mut ()) -> thread::Thread {
        // SAFETY: this is not safe.
        // However as long as it's the reverse of `thread_as_ptr` will work.
        unsafe { std::mem::transmute(ptr) }
    }
}
