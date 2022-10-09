#![feature(thread_id_value)]

use std::marker::PhantomData;
use std::num::NonZeroU64;
use std::ops::Deref;
use std::pin::Pin;
use std::sync::Arc;

/// Create a new left-right data structure.
///
/// # Safety
///
/// `left` and `right` **must** be equal.
pub unsafe fn new<T, O>(left: T, right: T) -> (Writer<T, O>, Handle<T>)
where
    O: Operation<T>,
{
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

    /// Flush all previously [applied] operations so that the readers can see
    /// the changes made.
    ///
    /// [applied]: Writer::apply
    pub fn flush(&mut self) {
        // SAFETY: we're the `Writer`.
        unsafe {
            self.shared
                .as_ref()
                .switch_reading(&mut self.last_seen_epochs)
        };

        // SAFETY: We're the `Writer`.
        let value = unsafe { self.shared.as_ref().writer_access_mut() };
        for operation in &self.log {
            operation.apply(&mut *value);
        }
        self.log.clear();
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
pub trait Operation<T> {
    /// Apply operation to `target`.
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
    /// impl<T> Operation<T> for Calculator
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
}

/// A handle to the left-right data structure that provides no access.
///
/// With this handle you can do three things:
///  * Move it to another thread ([`Reader`]s can't be moved across threads).
///  * Convert it into a [`Reader`].
///  * Cheaply [`clone`] it.
///
/// [`clone`]: Clone
#[derive(Clone)]
pub struct Handle<T> {
    shared: Pin<Arc<Shared<T>>>,
}

impl<T> Handle<T> {
    /// Turn this `Handle` into a `Reader`.
    pub fn into_reader(self) -> Reader<T> {
        let epoch_index = self.shared.as_ref().epoch_index();
        Reader {
            shared: self.shared,
            epoch_index,
            _not_send: PhantomData,
        }
    }
}

/// Read access to the left-right data structure.
///
/// A `Reader` is always bound to a thread and is thus not [`Send`], to move a
/// reader across first convert into a [`Handle`].
#[derive(Clone)]
pub struct Reader<T> {
    shared: Pin<Arc<Shared<T>>>,
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
    pub fn read<'a>(&'a self) -> ReadGuard<'a, T> {
        let shared = self.shared.as_ref();
        ReadGuard {
            value: shared.mark_reading(self.epoch_index),
            shared,
            epoch_index: self.epoch_index,
            _not_send: PhantomData,
        }
    }

    /// Create new a `Handle` from this `Reader` so it can be moved across
    /// threads.
    pub fn as_handle(&self) -> Handle<T> {
        Handle {
            shared: self.shared.clone(),
        }
    }

    /// Convert this `Reader` into a `Handle` so it can be moved across threads.
    pub fn into_handle(self) -> Handle<T> {
        Handle {
            shared: self.shared,
        }
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
    use std::pin::Pin;
    use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
    use std::sync::{Arc, RwLock};
    use std::{ptr, thread};

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
        /// This must always point to either `left` or `right` and must be valid for
        /// at least as long as `Shared` lives.
        read: AtomicPtr<T>,
        /// Epochs for the readers.
        read_epochs: RwLock<Vec<AtomicUsize>>,
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
            // SAFETY: caller must ensure we're the writer.
            let reading = &mut *self.reading.get();
            // Switch which copy the readers are accessing.
            self.read.store(
                match reading {
                    Reading::Left => {
                        *reading = Reading::Right;
                        &self.right
                    }
                    Reading::Right => {
                        *reading = Reading::Left;
                        &self.left
                    }
                } as *const _ as *mut _,
                Ordering::SeqCst,
            );

            // Get the current epochs.
            current_epochs.clear();
            current_epochs.extend(
                self.read_epochs
                    .read()
                    .unwrap()
                    .iter()
                    .map(|epoch| epoch.load(Ordering::SeqCst)),
            );

            // If one or more readers are currently accessing the our *now*
            // writer's copy (after the switch above) we have to wait for them
            // to increase their epoch, as that means they've stopped accessing
            // the copy. Note have that after that they can increase their epoch
            // *again*, but at that point they'll be accessing the *new*
            // reader's copy (as we switched above).
            //
            // So, we check if the current epoch (`ce`) is in a not-accessing
            // state (`% 2 == 0`) or if the new epoch (`ne`) is in a different
            // state then previously recorded (`ce != ne`). Note we use `!=`
            // instead of `>` because the epoch can wrap around (after 2^63
            // reads).
            loop {
                let no_readers = {
                    zip(
                        current_epochs.iter_mut(),
                        self.read_epochs.read().unwrap().iter(),
                    )
                    .all(|(ce, ne)| {
                        // If we know the reader is not accessing the value we
                        // don't have to load their epoch.
                        (*ce % 2 == 0) || {
                            let ne = ne.load(Ordering::SeqCst);
                            if *ce != ne {
                                *ce = 0; // Short circuit in the next iteration.
                                true
                            } else {
                                false
                            }
                        }
                    })
                };
                if no_readers {
                    // No more readers are accessing our *now* writer's copy, so
                    // we safely return ensure that only the writer has access
                    // to this copy.
                    return;
                }

                // FIXME: don't spin loop here.
                std::thread::yield_now()
            }
        }

        /// Returns the epoch index.
        pub(super) fn epoch_index(self: Pin<&Self>) -> NonZeroU64 {
            let index = thread::current().id().as_u64();
            let length_required = (index.get() + 1) as usize;
            if self.read_epochs.read().unwrap().len() < length_required {
                // Not enough epoch allocated, allocate them now.
                self.read_epochs
                    .write()
                    .unwrap()
                    .resize_with(length_required, || AtomicUsize::new(0));
            }
            index
        }

        /// Mark thread with `epoch_index` as reading.
        pub(super) fn mark_reading<'a>(self: Pin<&'a Self>, epoch_index: NonZeroU64) -> &'a T {
            let _ = self.read_epochs.read().unwrap()[epoch_index.get() as usize]
                .fetch_add(1, Ordering::SeqCst);
            // SAFETY: safe based on the requirements on `Shared.read`.
            unsafe { &*self.read.load(Ordering::SeqCst) }
        }

        /// Mark thread with `epoch_index` as done reading.
        pub(super) fn mark_done_reading(self: Pin<&Self>, epoch_index: NonZeroU64) {
            let _ = self.read_epochs.read().unwrap()[epoch_index.get() as usize]
                .fetch_add(1, Ordering::SeqCst);
        }
    }

    unsafe impl<T: Sync + Send> Sync for Shared<T> {}
    unsafe impl<T: Sync + Send> Send for Shared<T> {}
}

use shared::Shared;
