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
