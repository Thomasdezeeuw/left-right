//! Module with the [`Operation`] trait.

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

/// Operation that overwrites the value.
///
/// # Notes
///
/// An optimised implementation of the [`Log`] trait is available in
/// `Option<OverwriteOperation<T>>` when using this type.
pub struct OverwriteOperation<T> {
    value: T,
}

impl<T> OverwriteOperation<T> {
    /// Create a new `OverwriteOperation`.
    pub const fn new(value: T) -> OverwriteOperation<T> {
        OverwriteOperation { value }
    }
}

unsafe impl<T> Operation<T> for OverwriteOperation<T>
where
    T: Clone,
{
    fn apply(&self, target: &mut T) {
        target.clone_from(&self.value);
    }

    fn apply_again(self, target: &mut T) {
        *target = self.value;
    }
}

/// [`Operation`] Log.
///
/// Log of operations that need to be applied to the second copy after the same
/// operations have already been applied to the first copy.
///
/// The easiest and commonly used `Log` type is a `Vec`tor and will do a good
/// job in all cases. However extraction this a trait means we can optimise for
/// [`OverwriteOperation`].
pub unsafe trait Log<T>: Sized {
    type Operation: Operation<T>;

    /// Create a new empty log.
    fn new() -> Self;

    /// Returns true if the log is empty, false otherwise.
    ///
    /// # Correctness
    ///
    /// This is used as an optimisation to determine when the log doesn't have
    /// to be applied to the second copy. If this incorrectly returns true the
    /// two copies might get out of sync.
    fn is_empty(&self) -> bool;

    /// Add `operation` to the log.
    fn push(&mut self, operation: Self::Operation);

    /// Apply all operations in the log to `target` and clear the log.
    ///
    /// # Correctness
    ///
    /// All operations in the log must be applied to ensure both copies are in
    /// sync.
    fn apply_and_clear(&mut self, target: &mut T)
    where
        Self: Sized;
}

unsafe impl<O, T> Log<T> for Vec<O>
where
    O: Operation<T>,
{
    type Operation = O;

    fn new() -> Self {
        Vec::new()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn push(&mut self, operation: Self::Operation) {
        self.push(operation);
    }

    fn apply_and_clear(&mut self, target: &mut T)
    where
        Self: Sized,
    {
        for operation in self.drain(..) {
            operation.apply_again(target);
        }
    }
}

/// Optimisation for [`OverwriteOperation`] where we only store the last
/// operation as it completely overwrites the value.
unsafe impl<T> Log<T> for Option<OverwriteOperation<T>>
where
    T: Clone,
{
    type Operation = OverwriteOperation<T>;

    fn new() -> Self {
        None
    }

    fn is_empty(&self) -> bool {
        self.is_none()
    }

    fn push(&mut self, operation: Self::Operation) {
        *self = Some(operation);
    }

    fn apply_and_clear(&mut self, target: &mut T)
    where
        Self: Sized,
    {
        if let Some(operation) = self.take() {
            operation.apply_again(target)
        }
    }
}
