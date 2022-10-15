//! Left-right hashmap.
//!
//! # Examples
//!
//! This example shows that writes made by the writer are not visible to the
//! reader until they are [flushed].
//!
//! [flushed]: Writer::flush
//!
//! ```
//! let (mut writer, handle) = hashmap::new();
//! let handle2 = handle.clone();
//! let mut reader1 = handle.into_reader();
//!
//! // Add a value to the writer's copy.
//! writer.insert("key", "value");
//! assert_eq!(writer.len(), 1);
//!
//! // We create a `ReadGuard` to get a consistent view of the map.
//! // SAFETY: we can only have a single `ReadGuard` alive per thread.
//! let read_guard1 = unsafe { reader1.read() };
//! // The readers can't see the value yet, because the writer didn't flush them
//! // yet.
//! assert!(!read_guard1.contains_key("key"));
//! assert!(read_guard1.is_empty());
//!
//! # let handle1 =
//! std::thread::spawn(move || {
//!     // Only after the writer flushes, the changes become visible to the
//!     // readers. This will block until all readers stopped reading the
//!     // current version. This will happen once all read guards are dropped.
//!     writer.flush();
//! });
//! #
//! # // Yey, sleep based concurrency!
//! # std::thread::sleep(std::time::Duration::from_millis(10));
//!
//! # let handle2 =
//! std::thread::spawn(move || {
//!     // NOTE: this would NOT be safe to do on the main thread while
//!     // `read_guard1` is alive.
//!     let reader2 = handle2.into_reader();
//!     // After the writer flushed the change they are visible to the readers.
//!     assert_eq!(reader2.contains_key("key"), true);
//!     assert_eq!(reader2.len(), 1);
//! });
//!
//! // However readers that started reading before the writes were flushed will
//! // still see old values. This ensures the readers get a consistent view of
//! // the map, albeit (slightly) outdated.
//! assert!(!read_guard1.contains_key("key"));
//! assert!(read_guard1.is_empty());
//!
//! // To get an updated view simply drop the read guard and continue using the
//! // reader. Blocking the read guard will unblock the writer's call to flush.
//! drop(read_guard1);
//! assert_eq!(reader1.get("key"), Some("value"));
//! assert_eq!(reader1.len(), 1);
//! #
//! # handle1.join().unwrap();
//! # handle2.join().unwrap();
//! ```

use std::borrow::Borrow;
use std::collections::hash_map::{HashMap, RandomState};
use std::hash::{BuildHasher, Hash};
use std::ops::Deref;

/// Create a new hashmap.
pub fn new<K, V>() -> (Writer<K, V>, Handle<K, V>) {
    with_hasher(RandomState::default())
}

/// Creates an empty hashmap with at least the specified `capacity`.
pub fn with_capacity<K, V>(capacity: usize) -> (Writer<K, V>, Handle<K, V>) {
    with_capacity_and_hasher(capacity, RandomState::default())
}

/// Creates an empty hashmap which will use the given hash builder to hash keys.
pub fn with_hasher<K, V, S>(hasher: S) -> (Writer<K, V, S>, Handle<K, V, S>)
where
    S: Clone,
{
    let left = HashMap::with_hasher(hasher.clone());
    let right = HashMap::with_hasher(hasher);
    // SAFETY: `left` and `right` are the same.
    let (writer, handle) = unsafe { left_right::new(left, right) };
    (Writer { inner: writer }, Handle { inner: handle })
}

/// Creates an empty hashmap with at least the specified `capacity`, using
/// `hasher` to hash the keys.
pub fn with_capacity_and_hasher<K, V, S>(
    capacity: usize,
    hasher: S,
) -> (Writer<K, V, S>, Handle<K, V, S>)
where
    S: Clone,
{
    let left = HashMap::with_capacity_and_hasher(capacity, hasher.clone());
    let right = HashMap::with_capacity_and_hasher(capacity, hasher);
    // SAFETY: `left` and `right` are the same.
    let (writer, handle) = unsafe { left_right::new(left, right) };
    (Writer { inner: writer }, Handle { inner: handle })
}

/// Write access to the hashmap.
///
/// Write access is limited to insertions and removals.
///
/// # Examples
///
/// This example shows that writes made by the writer are not visible to the
/// reader until they are [flushed].
///
/// [flushed]: Writer::flush
///
/// ```
/// let (mut writer, handle) = hashmap::new();
/// let mut reader = handle.into_reader();
///
/// writer.insert("key", "value");
/// assert_eq!(writer.len(), 1);
///
/// // The reader can't see the value yet.
/// assert!(!reader.contains_key("key"));
/// assert!(reader.is_empty());
///
/// // After the writer flushes the changes become visible to the readers.
/// writer.flush();
/// assert_eq!(reader.get("key"), Some("value"));
/// assert_eq!(reader.len(), 1);
/// ```
pub struct Writer<K, V, S = RandomState> {
    inner: left_right::Writer<HashMap<K, V, S>, Operation<K, V>>,
}

/// Writer [operation] for [`Writer`].
///
/// [operation]: left_right::Operation
enum Operation<K, V> {
    Reserve(usize),
    ShrinkToFit,
    ShrinkTo(usize),
    Insert(K, V),
    Remove(K),
    Clear,
}

impl<K, V, S> left_right::Operation<HashMap<K, V, S>> for Operation<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
    S: BuildHasher,
{
    fn apply(&self, target: &mut HashMap<K, V, S>) {
        match self {
            Operation::Reserve(additional) => target.reserve(*additional),
            Operation::ShrinkToFit => target.shrink_to_fit(),
            Operation::ShrinkTo(min_capacity) => target.shrink_to(*min_capacity),
            Operation::Insert(key, value) => {
                let _ = target.insert(key.clone(), value.clone());
            }
            Operation::Remove(key) => {
                let _ = target.remove(&key);
            }
            Operation::Clear => target.clear(),
        }
    }

    fn apply_again(self, target: &mut HashMap<K, V, S>)
    where
        Self: Sized,
    {
        match self {
            Operation::Reserve(additional) => target.reserve(additional),
            Operation::ShrinkToFit => target.shrink_to_fit(),
            Operation::ShrinkTo(min_capacity) => target.shrink_to(min_capacity),
            Operation::Insert(key, value) => {
                let _ = target.insert(key, value);
            }
            Operation::Remove(key) => {
                let _ = target.remove(&key);
            }
            Operation::Clear => target.clear(),
        }
    }
}

impl<K, V, S> Writer<K, V, S>
where
    K: Clone + Eq + Hash,
    V: Clone,
    S: BuildHasher,
{
    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the hash map.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.apply(Operation::Reserve(additional));
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.inner.apply(Operation::ShrinkToFit)
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.apply(Operation::ShrinkTo(min_capacity))
    }

    /// Inserts a key-value pair into the map.
    ///
    /// # Notes
    ///
    /// To make this available to the readers you have to call [`flush`] first.
    ///
    /// [`flush`]: Writer::flush
    pub fn insert(&mut self, key: K, value: V) {
        self.inner.apply(Operation::Insert(key, value));
    }

    /// Removes `key` from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Notes
    ///
    /// To make this available to the readers you have to call [`flush`] first.
    ///
    /// [`flush`]: Writer::flush
    pub fn remove(&mut self, key: K) -> Option<V> {
        let value = unsafe { self.inner.access_mut().remove(&key) };
        if value.is_some() {
            unsafe { self.inner.apply_to_reader_copy(Operation::Remove(key)) }
        }
        value
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Notes
    ///
    /// To make this available to the readers you have to call [`flush`] first.
    ///
    /// [`flush`]: Writer::flush
    pub fn clear(&mut self) {
        self.inner.apply(Operation::Clear);
    }

    /// Flush all previously made changes so that the readers can see them.
    pub fn flush(&mut self) {
        self.inner.flush();
    }
}

impl<K, V, S> Deref for Writer<K, V, S> {
    type Target = HashMap<K, V, S>;

    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

/// A handle to the hashmap that provides no access.
///
/// With this handle you can do three things:
///  * Move it to another thread ([`Reader`]s can't be moved across threads).
///  * Convert it into a [`Reader`].
///  * Cheaply [`clone`] it.
///
/// [`clone`]: Clone
#[derive(Clone)]
pub struct Handle<K, V, S = RandomState> {
    inner: left_right::Handle<HashMap<K, V, S>>,
}

impl<K, V, S> Handle<K, V, S> {
    /// Turn this `Handle` into a `Reader`.
    pub fn into_reader(self) -> Reader<K, V, S> {
        Reader {
            inner: self.inner.into_reader(),
        }
    }
}

/// Read access to the hashmap.
///
/// A `Reader` is always bound to a thread and is thus not [`Send`], to move a
/// reader across first convert into a [`Handle`].
pub struct Reader<K, V, S = RandomState> {
    inner: left_right::Reader<HashMap<K, V, S>>,
}

impl<K, V, S> Reader<K, V, S> {
    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        unsafe { self.read().len() }
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        unsafe { self.read().is_empty() }
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        unsafe { self.read().capacity() }
    }

    /// Returns all keys.
    pub fn keys(&self) -> Vec<K>
    where
        K: Clone,
    {
        unsafe { self.read().keys().cloned().collect() }
    }

    /// Returns itself as a clone of the underlying `HashMap`.
    pub fn as_hashmap(&self) -> HashMap<K, V, S>
    where
        K: Clone,
        V: Clone,
        S: Clone,
    {
        unsafe { self.read().clone() }
    }

    /// Create new a `Handle` from this `Reader` so it can be moved across
    /// threads.
    pub fn as_handle(&self) -> Handle<K, V, S> {
        Handle {
            inner: self.inner.as_handle(),
        }
    }

    /// Convert this `Reader` into a `Handle` so it can be moved across threads.
    pub fn into_handle(self) -> Handle<K, V, S> {
        Handle {
            inner: self.inner.into_handle(),
        }
    }

    /// Get read access to the data structure.
    ///
    /// While the returned `ReadGuard` lives it will block the flushing of all
    /// writes.
    ///
    /// # Safety
    ///
    /// At most one `ReadGuard` may be alive per thread. No other method on the
    /// type may be called while the `ReadGuard` is alive on this thread.
    pub unsafe fn read<'a>(&'a self) -> ReadGuard<'a, K, V, S> {
        ReadGuard {
            inner: self.inner.read(),
        }
    }
}

impl<K, V, S> Reader<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Returns a clone of to the value corresponding to the `key`.
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        V: Clone,
    {
        unsafe { self.read().get(key).cloned() }
    }

    /// Returns `true` if the map contains a value for the specified `key`.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        unsafe { self.read().contains_key(key) }
    }
}

impl<K, V, S> Clone for Reader<K, V, S> {
    fn clone(&self) -> Reader<K, V, S> {
        Reader {
            inner: self.inner.clone(),
        }
    }

    fn clone_from(&mut self, source: &Reader<K, V, S>) {
        self.inner = source.inner.clone();
    }
}

/// Similar to a mutex guard this protects the data structure so that the read
/// access is properly synchronised with possible concurrent writes.
///
/// # Safety
///
/// At most one `ReadGuard` may be alive per thread.
pub struct ReadGuard<'a, K, V, S> {
    inner: left_right::ReadGuard<'a, HashMap<K, V, S>>,
}

impl<'a, K, V, S> Deref for ReadGuard<'a, K, V, S> {
    type Target = HashMap<K, V, S>;

    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}
