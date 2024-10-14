/// Constructs a [`struct@Sum`] type from a list of types.
///
/// # Examples
///
/// ```rust
/// use tsum::Sum;
///
/// type MySum = Sum![i32, u32, f64];
/// let s: MySum = Sum::new(42u32);
/// ```
#[macro_export]
macro_rules! Sum {
    [$($t:ty),* $(,)?] => [$crate::Sum::<$crate::T![$($t,)*]>];
}

/// Constructs a tuple list (heterogeneous list) type from a list of types.
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
#[macro_export]
macro_rules! T {
    [] => [()];
    [$head:ty $(, $t:ty)* $(,)?] => [($head, $crate::T!($($t,)*))];
}

/// Constructs a tuple list (heterogeneous list) value from a list of values.
///
/// The type version of the macro is [`T`].
///
/// # Examples
///
/// ```rust
/// use tsum::t;
///
/// type MyList = (i32, (u32, (f64, ())));
/// let list: MyList = t![42i32, 42u32, 42.0f64];
#[macro_export]
macro_rules! t {
    [] => [()];
    [$head:expr $(, $t:expr)* $(,)?] => [($head, $crate::t!($($t,)*))];
}
