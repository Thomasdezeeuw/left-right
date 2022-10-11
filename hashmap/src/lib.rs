//! Left-right hashmap.

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
    /// Get read access to the data structure.
    ///
    /// While the returned `ReadGuard` lives it will block the flushing of all
    /// writes.
    pub fn read<'a>(&'a self) -> ReadGuard<'a, K, V, S> {
        ReadGuard {
            inner: self.inner.read(),
        }
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
}

/// Similar to a mutex guard this protects the data structure so that the read
/// access is properly synchronised with possible concurrent writes.
pub struct ReadGuard<'a, K, V, S> {
    inner: left_right::ReadGuard<'a, HashMap<K, V, S>>,
}

impl<'a, K, V, S> Deref for ReadGuard<'a, K, V, S> {
    type Target = HashMap<K, V, S>;

    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}
