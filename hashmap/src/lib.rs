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
//! let mut reader1 = handle.into_reader();
//! let mut reader2 = reader1.clone();
//!
//! // Add a value to the writer's copy.
//! writer.insert("key", "value");
//! assert_eq!(writer.len(), 1);
//!
//! // The readers can't see the value yet.
//! let read_guard1 = reader1.read();
//! assert!(read_guard1.get("key").is_none());
//! assert_eq!(read_guard1.len(), 0);
//!
//! let handle = std::thread::spawn(move || {
//!     // After the writer flushes the changes become visible to the readers.
//!     // This will block until all readers stopped reading the current
//!     // version. This will happen once all read guard are dropped.
//!     writer.flush();
//! });
//! #
//! # // Yey sleep based concurrency!
//! # std::thread::sleep(std::time::Duration::from_millis(10));
//!
//! // After the writer flushed the change they are visible to the readers.
//! let read_guard2 = reader2.read();
//! assert_eq!(read_guard2.get("key"), Some(&"value"));
//! assert_eq!(read_guard2.len(), 1);
//! drop(read_guard2);
//!
//! // However readers that started reading before the writes were flushes will
//! // still see old values. This ensures the readers get a consistent view of
//! // the map, albeit (slightly) outdated.
//! assert!(read_guard1.get("key").is_none());
//! assert_eq!(read_guard1.len(), 0);
//! drop(read_guard1); // This unblocks the writer's call to flush.
//!
//! // To get an updated view simply drop the read guard and get another one.
//! let read_guard1 = reader1.read();
//! assert_eq!(read_guard1.get("key"), Some(&"value"));
//! assert_eq!(read_guard1.len(), 1);
//! drop(read_guard1);
//!
//! # handle.join().unwrap();
//! ```

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
/// let r = reader.read();
/// assert!(r.get("key").is_none());
/// assert_eq!(r.len(), 0);
/// drop(r);
///
/// // After the writer flushes the changes become visible to the readers.
/// writer.flush();
/// let r = reader.read();
/// assert_eq!(r.get("key"), Some(&"value"));
/// assert_eq!(r.len(), 1);
/// drop(r);
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

    /// Removes a key from the map.
    ///
    /// # Notes
    ///
    /// To make this available to the readers you have to call [`flush`] first.
    ///
    /// [`flush`]: Writer::flush
    pub fn remove(&mut self, key: K) {
        self.inner.apply(Operation::Remove(key));
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
#[derive(Clone)]
pub struct Reader<K, V, S = RandomState> {
    inner: left_right::Reader<HashMap<K, V, S>>,
}

impl<K, V, S> Reader<K, V, S> {
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
}
