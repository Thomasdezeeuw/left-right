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
//! let (mut writer, handle) = left_right::hashmap::new();
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
//!     writer.blocking_flush();
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
//! // reader. Dropping the read guard will unblock the writer's call to flush.
//! drop(read_guard1);
//! assert_eq!(reader1.get_cloned("key"), Some("value"));
//! assert_eq!(reader1.len(), 1);
//! #
//! # handle1.join().unwrap();
//! # handle2.join().unwrap();
//! ```

use std::borrow::Borrow;
use std::collections::hash_map::{Drain, HashMap, RandomState};
use std::future::Future;
use std::hash::{BuildHasher, Hash};
use std::ops::Deref;

/// Create a new hashmap.
pub fn new<K, V>() -> (Writer<K, V>, Handle<K, V>)
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    with_hasher(RandomState::default())
}

/// Creates an empty hashmap with at least the specified `capacity`.
pub fn with_capacity<K, V>(capacity: usize) -> (Writer<K, V>, Handle<K, V>)
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    with_capacity_and_hasher(capacity, RandomState::default())
}

/// Creates an empty hashmap which will use the given hash builder to hash keys.
pub fn with_hasher<K, V, S>(hasher: S) -> (Writer<K, V, S>, Handle<K, V, S>)
where
    K: Clone + Eq + Hash,
    V: Clone,
    S: BuildHasher + Clone,
{
    let left = HashMap::with_hasher(hasher.clone());
    let right = HashMap::with_hasher(hasher);
    // SAFETY: `left` and `right` are the same.
    let (writer, handle) = unsafe { crate::new(left, right) };
    (Writer { inner: writer }, Handle { inner: handle })
}

/// Creates an empty hashmap with at least the specified `capacity`, using
/// `hasher` to hash the keys.
pub fn with_capacity_and_hasher<K, V, S>(
    capacity: usize,
    hasher: S,
) -> (Writer<K, V, S>, Handle<K, V, S>)
where
    K: Clone + Eq + Hash,
    V: Clone,
    S: BuildHasher + Clone,
{
    let left = HashMap::with_capacity_and_hasher(capacity, hasher.clone());
    let right = HashMap::with_capacity_and_hasher(capacity, hasher);
    // SAFETY: `left` and `right` are the same.
    let (writer, handle) = unsafe { crate::new(left, right) };
    (Writer { inner: writer }, Handle { inner: handle })
}

/// Write access to the hashmap.
///
/// # Notes
///
/// Any changes made to the `Writer` are not available to the readers until
/// [`Writer::flush`] is called.
///
/// # Examples
///
/// This example shows that writes made by the writer are not visible to the
/// reader until they are [flushed].
///
/// [flushed]: Writer::flush
///
/// ```
/// let (mut writer, handle) = left_right::hashmap::new();
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
/// writer.blocking_flush();
/// assert_eq!(reader.get_cloned("key"), Some("value"));
/// assert_eq!(reader.len(), 1);
/// ```
pub struct Writer<K, V, S = RandomState> {
    inner: crate::Writer<HashMap<K, V, S>, Vec<Operation<K, V>>>,
}

/// Writer [operation] for [`Writer`].
///
/// [operation]: crate::Operation
enum Operation<K, V> {
    Reserve(usize),
    ShrinkToFit,
    ShrinkTo(usize),
    Insert(K, V),
    Remove(K),
    Clear,
}

unsafe impl<K, V, S> crate::Operation<HashMap<K, V, S>> for Operation<K, V>
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
                let _ = target.remove(key);
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

    /// Inserts a key-value pair into the map, returning the old value if any.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        // SAFETY: we're replicating the insert below.
        let old_value = unsafe { self.inner.access_mut().insert(key.clone(), value.clone()) };
        unsafe {
            self.inner
                .apply_to_reader_copy(Operation::Insert(key, value))
        }
        old_value
    }

    /// Removes `key` from the map, returning the value at the key if the key
    /// was previously in the map.
    pub fn remove(&mut self, key: K) -> Option<V> {
        // SAFETY: we're replicating the remove below.
        let value = unsafe { self.inner.access_mut().remove(&key) };
        if value.is_some() {
            unsafe { self.inner.apply_to_reader_copy(Operation::Remove(key)) }
        }
        value
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    pub fn remove_entry(&mut self, key: K) -> Option<(K, V)> {
        // SAFETY: we're replicating the remove below.
        let value = unsafe { self.inner.access_mut().remove_entry(&key) };
        if value.is_some() {
            unsafe { self.inner.apply_to_reader_copy(Operation::Remove(key)) }
        }
        value
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    pub fn drain<'a>(&'a mut self) -> Drain<'a, K, V> {
        // SAFETY: we're replicating the clear below with `drain`.
        unsafe { self.inner.apply_to_reader_copy(Operation::Clear) }
        unsafe { self.inner.access_mut().drain() }
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    pub fn clear(&mut self) {
        self.inner.apply(Operation::Clear);
    }

    /// Flush all previously made changes so that the readers can see them.
    pub fn blocking_flush(&mut self) {
        self.inner.blocking_flush();
    }

    /// Asynchronously flush all previously made changes so that the readers can
    /// see them.
    pub fn flush<'a>(&'a mut self) -> impl Future<Output = ()> + 'a {
        self.inner.flush()
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
/// See [`left_right::Handle`] for more information on usage.
///
/// [`left_right::Handle`]: crate::Handle
#[derive(Clone)]
pub struct Handle<K, V, S = RandomState> {
    inner: crate::Handle<HashMap<K, V, S>>,
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
/// reader across thread bounds first convert it into a [`Handle`].
pub struct Reader<K, V, S = RandomState> {
    inner: crate::Reader<HashMap<K, V, S>>,
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
    pub fn keys_cloned(&self) -> Vec<K>
    where
        K: Clone,
    {
        unsafe { self.read().keys().cloned().collect() }
    }

    /// Returns all values.
    pub fn values_cloned(&self) -> Vec<V>
    where
        V: Clone,
    {
        unsafe { self.read().values().cloned().collect() }
    }

    /// Returns all key-value pairs.
    pub fn key_values_cloned(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        unsafe {
            self.read()
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect()
        }
    }

    /// Returns itself as a clone of the underlying `HashMap`.
    pub fn clone_hashmap(&self) -> HashMap<K, V, S>
    where
        K: Clone,
        V: Clone,
        S: Clone,
    {
        unsafe { self.read().clone() }
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
    pub unsafe fn read<'a>(&'a self) -> crate::ReadGuard<'a, HashMap<K, V, S>> {
        self.inner.read()
    }
}

impl<K, V, S> Reader<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Returns a clone of to the value corresponding to the `key`.
    pub fn get_cloned<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        V: Clone,
    {
        unsafe { self.read().get(key).cloned() }
    }

    /// Returns a clone of to the key-value pair corresponding to the `key`.
    pub fn get_key_value_cloned<Q>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Clone + Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        V: Clone,
    {
        unsafe {
            self.read()
                .get_key_value(key)
                .map(|(k, v)| (k.clone(), v.clone()))
        }
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
        self.inner.clone_from(&source.inner);
    }
}
