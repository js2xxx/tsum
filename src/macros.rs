/// Declares an ordered [`Sum`] type.
///
/// Each entry is a distinct variant, and a type may appear more than once.
/// `Sum![]` is the empty sum.
///
/// # Examples
///
/// ```rust
/// use tsum::Sum;
///
/// type MySum = Sum![i32, u32, f64];
/// let s: MySum = Sum::new(42u32);
/// assert_eq!(s.get::<u32, _>(), Some(&42));
/// ```
///
/// [`Sum`]: crate::sum::Sum
#[macro_export]
macro_rules! Sum {
    [$($t:ty),* $(,)?] => [$crate::sum::Sum::<$crate::T![$($t,)*]>];
}

/// Declares a [`Union`](struct@crate::Union) type.
///
/// Each member must implement [`Element`](trait@crate::union::Element) and have
/// a distinct element ID. `Union![]` is the empty union.
///
/// # Examples
///
/// ```rust
/// use tsum::Union;
///
/// type MyUnion = Union![i32, u32, f64];
/// let u: MyUnion = Union::new(42u32);
/// assert_eq!(u.get::<u32>(), Some(&42));
/// ```
#[macro_export]
macro_rules! Union {
    [$($t:ty),* $(,)?] => [$crate::union::Union::<$crate::T![$($t,)*]>];
}

/// Names a tuple list of types.
///
/// Use it for a subset in `value.narrow::<T![A, B], _>()` on a
/// [`Sum`](struct@crate::Sum), or as the member list in `Union<T![A, B]>`.
/// `T![]` is `()`.
///
/// The value version of the macro is [`t`].
///
/// # Examples
///
/// ```rust
/// use tsum::T;
///
/// type MyList = T![i32, u32, f64];
/// let list: MyList = (42i32, (42u32, (42.0f64, ())));
/// ```
///
/// [`t`]: crate::t
#[macro_export]
macro_rules! T {
    [] => [()];
    [$head:ty $(, $t:ty)* $(,)?] => [($head, $crate::T!($($t,)*))];
}

/// Builds a tuple list of values in the given order.
///
/// `t![]` evaluates to `()`.
///
/// The type version of the macro is [`T`].
///
/// # Examples
///
/// ```rust
/// use tsum::t;
///
/// let list: tsum::T![i32, bool] = t![42i32, true];
/// assert_eq!(list, (42, (true, ())));
/// ```
///
/// [`T`]: crate::T
#[macro_export]
macro_rules! t {
    [] => [()];
    [$head:expr $(, $t:expr)* $(,)?] => [($head, $crate::t!($($t,)*))];
}
