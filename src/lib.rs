//! THE true generic sum type for Rust.
//!
//! # Usage
//!
//! Manipulating with values:
//!
//! ```rust
//! type Sum1 = tsum::Sum![u32, usize, String, Vec<u8>];
//!
//! let v1: Sum1 = Sum1::new(1u32);
//! let mut v2: Sum1 = Sum1::new(2usize);
//! let v3: Sum1 = Sum1::new("hello".to_string());
//! let v4: Sum1 = Sum1::new(vec![1, 2, 3]);
//!
//! assert_eq!(v4.get(), Some(&vec![1, 2, 3]));
//! assert_eq!(v2.get::<u32, _>(), None);
//! assert_eq!(v2.get_mut::<usize, _>(), Some(&mut 2usize));
//!
//! // The code below will not compile
//! // because the type `()` is not a member of `Sum1`.
//! //
//! // assert_eq!(v2.get::<(), _>(), None);
//! ```
//!
//! Manipulating with type lists:
//!
//! ```rust
//! use tsum::{Sum, T};
//!
//! type Sum1 = Sum![u32, usize, String, Vec<u8>];
//! type Sum2 = Sum![u32, usize, Vec<u8>];
//! type Sum3 = Sum![u32, usize, i64, Vec<u8>];
//!
//! let sum: Sum1 = Sum1::new(42u32);
//!
//! // Broadening or narrowing a sum type is very easy:
//! let sum: Sum2 = sum.narrow().unwrap();
//! let sum: Sum3 = sum.broaden();
//!
//! // Failed operations also shrinks its type list to a subset.
//! let sum: Sum2 = sum.try_unwrap::<i64, _>().unwrap_err();
//! let value: u32 = sum.try_unwrap().unwrap();
//! assert_eq!(value, 42);
//!
//! let sum: Sum1 = Sum1::new("hello".to_string());
//! let sum: Sum3 = sum.map(|s: String| s.as_bytes()[0] as i64);
//! assert_eq!(sum, Sum3::new(104i64));
//! ```
//!
//! Interacting with common traits:
//!
//! ```rust
//! use tsum::{Sum, T};
//!
//! type Sum1 = Sum![u32, usize, String];
//!
//! fn assert_send_sync<T: Send + Sync>(_: T) {}
//!
//! assert_send_sync(Sum1::new(42u32));
//! assert_send_sync(Sum1::new("hello".to_string()));
//!
//! let sum: Sum1 = Sum::new(42usize);
//!
//! let cloned = sum.clone();
//! assert!(sum != Sum::new(42u32));
//! assert_eq!(format!("{sum}"), "42");
//! ```
//!
//! # Implementation details
//!
//! See the [`repr`] module for more details.

#![no_std]
#![deny(future_incompatible)]
#![deny(rust_2018_idioms)]
#![deny(rust_2024_compatibility)]
#![allow(edition_2024_expr_fragment_specifier)]
#![warn(missing_docs)]

#[cfg(test)]
extern crate std;

use core::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr,
};

mod derive;
pub mod repr;
pub mod tag;

use self::tag::{Tag, UTerm};

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

/// The true generic representation of a sum type.
///
/// See the [crate-level] documentation for more information.
///
/// # Examples
///
/// ```rust
/// use tsum::Sum;
///
/// let s: Sum![i32, u32, f64] = Sum::new(42u32);
/// ```
///
/// [crate-level]: crate
pub struct Sum<S: repr::SumList> {
    tag: u8,
    data: ManuallyDrop<S::Repr>,
}

impl<T> From<T> for Sum![T] {
    /// Constructs a `Sum` of one type from a value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32] = 42.into();
    /// assert_eq!(*s, 42);
    /// ```
    fn from(value: T) -> Self {
        Sum::new(value)
    }
}

impl<T> Deref for Sum![T] {
    type Target = T;

    /// Dereferences the `Sum` immutably to its inner value.
    ///
    /// This function can only be called on `Sum`s of one type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32] = 42.into();
    /// assert_eq!(*s, 42);
    fn deref(&self) -> &Self::Target {
        unsafe { &*<(T, ()) as repr::Split<T, UTerm>>::as_ptr(&self.data) }
    }
}

impl<T> DerefMut for Sum![T] {
    /// Dereferences the `Sum` mutably to its inner value.
    ///
    /// This function can only be called on `Sum`s of one type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let mut s: Sum![i32] = 42.into();
    /// *s += 1;
    /// assert_eq!(*s, 43);
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *<(T, ()) as repr::Split<T, UTerm>>::as_mut_ptr(&mut self.data) }
    }
}

impl<T> Sum![T] {
    /// Transforms the `Sum` type into its inner value.
    ///
    /// This function can only be called on `Sum`s of one type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32] = 42.into();
    /// assert_eq!(s.into_inner(), 42);
    pub fn into_inner(self) -> T {
        unsafe {
            let this = ManuallyDrop::new(self);
            mem::transmute_copy(&this.data)
        }
    }
}

impl Sum![] {
    /// Instantiates a never type from an empty `Sum`.
    ///
    /// This is useful for marking out branches of code that are unreachable
    /// at compile time without using [`unreachable!`] or sorts.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let _closure = |s: Sum![]| -> ! {
    ///     s.unreachable()
    /// };
    ///
    /// // This closure cannot be called because an empty `Sum` is uninhabited.
    /// ```
    pub fn unreachable(self) -> ! {
        match self.data.0 {}
    }
}

impl<S: repr::SumList> Sum<S> {
    /// Returns the type ID of the inhabited value.
    ///
    /// The result of this function is different of calling [`TypeId::of`],
    /// which returns the type ID of the `Sum` type itself.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// assert_eq!(s.type_id(), core::any::TypeId::of::<i32>());
    /// ```
    ///
    /// [`TypeId::of`]: core::any::TypeId::of
    pub fn type_id(&self) -> core::any::TypeId
    where
        S: derive::TypeMeta + 'static,
    {
        S::type_id(self.tag)
    }

    /// Returns the name of the type of the inhabited value.
    ///
    /// The result of this function is different of calling
    /// [`core::any::type_name`], which returns the type name of the `Sum` type
    /// itself.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// assert_eq!(s.type_name(), "i32");
    /// ```
    ///
    /// [`core::any::type_name`]: core::any::type_name
    pub fn type_name(&self) -> &'static str
    where
        S: derive::TypeMeta,
    {
        S::type_name(self.tag)
    }

    /// Coerces the reference of the inhabited value immutably into the dynamic
    /// type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// assert_eq!(s.as_any().downcast_ref::<i32>(), Some(&42));
    pub fn as_any(&self) -> &dyn core::any::Any
    where
        S: derive::TypeMeta + 'static,
    {
        unsafe { S::as_any(&self.data, self.tag) }
    }

    /// Coerces the reference of the inhabited value mutably into the dynamic
    /// type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let mut s: Sum![i32, u64, String] = Sum::new(42i32);
    /// *s.as_mut_any().downcast_mut::<i32>().unwrap() += 1;
    /// assert_eq!(s.get(), Some(&43i32));
    /// ```
    pub fn as_mut_any(&mut self) -> &mut dyn core::any::Any
    where
        S: derive::TypeMeta + 'static,
    {
        unsafe { S::as_mut_any(&mut self.data, self.tag) }
    }
}

impl<S: repr::SumList> Sum<S> {
    /// Constructs a new `Sum` from the given value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// assert_eq!(s.get(), Some(&42i32));
    /// ```
    pub fn new<T, U>(value: T) -> Self
    where
        S: repr::Split<T, U>,
        U: Tag,
    {
        Sum {
            tag: U::VALUE,
            data: ManuallyDrop::new(S::from_data(value)),
        }
    }

    /// Constructs a new `Sum` from the given value and a marker of its type
    /// lists.
    ///
    /// This is useful when the type information is not known at macro
    /// expansion. It can be used in pairs with [`Sum::type_marker`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::marker::PhantomData;
    /// use tsum::{Sum, T};
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// let s2 = Sum::new_marked(42i32, s.type_marker());
    /// assert_eq!(s, s2);
    /// ```
    pub fn new_marked<T, U>(value: T, _: PhantomData<S>) -> Self
    where
        S: repr::Split<T, U>,
        U: Tag,
    {
        Self::new(value)
    }

    /// Returns a marker of the type list of the `Sum`.
    ///
    /// This is useful when the type information is not known at macro
    /// expansion. It can be used in pairs with [`Sum::new_marked`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::marker::PhantomData;
    /// use tsum::{Sum, T};
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// let s2 = Sum::new_marked(42i32, s.type_marker());
    /// assert_eq!(s, s2);
    /// ```
    pub fn type_marker(&self) -> PhantomData<S> {
        PhantomData
    }

    /// Returns an immutable reference to the value if the `Sum` is inhabited
    /// with the specified type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// assert_eq!(s.get(), Some(&42i32));
    /// ```
    pub fn get<T, U>(&self) -> Option<&T>
    where
        S: repr::Split<T, U>,
        U: Tag,
    {
        (self.tag == U::VALUE).then(|| unsafe { &*S::as_ptr(&self.data) })
    }

    /// Returns a mutable reference to the value if the `Sum` is inhabited
    /// with the specified type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let mut s: Sum![i32, u64, String] = Sum::new(42i32);
    /// *s.get_mut::<i32, _>().unwrap() += 1;
    /// assert_eq!(s.get(), Some(&43i32));
    /// ```
    pub fn get_mut<T, U>(&mut self) -> Option<&mut T>
    where
        S: repr::Split<T, U>,
        U: Tag,
    {
        (self.tag == U::VALUE).then(|| unsafe { &mut *S::as_mut_ptr(&mut self.data) })
    }

    /// Performs the given function if the `Sum` is inhabited with the specified
    /// type.
    ///
    /// This function can be called in chain.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// let s = s.inspect(|value: &i32| assert_eq!(value, &42i32))
    ///     .inspect(|value: &u64| assert_eq!(value, &236u64))
    ///     .inspect(|value: &String| assert_eq!(value, &"whatever".to_string()));
    /// ```
    pub fn inspect<T, U, F>(self, f: F) -> Self
    where
        S: repr::Split<T, U>,
        U: Tag,
        F: FnOnce(&T),
    {
        if let Some(value) = self.get() {
            f(value);
        }
        self
    }

    /// Performs the given function if the `Sum` is inhabited with the specified
    /// type.
    ///
    /// This function can be called in chain.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// let s = s.inspect_mut(|value: &mut i32| *value += 1);
    /// assert_eq!(s.get(), Some(&43i32));
    /// ```
    pub fn inspect_mut<T, U, F>(mut self, f: F) -> Self
    where
        S: repr::Split<T, U>,
        U: Tag,
        F: FnOnce(&mut T),
    {
        if let Some(value) = self.get_mut() {
            f(value);
        }
        self
    }
}

/// The remainder type list from splitting type list `S` with type `T` and its
/// index tag `U`.
pub type Rem<S, T, U> = <S as repr::Split<T, U>>::Remainder;

/// The remainder index tag map from splitting type list `S` with type `T` and
/// its index tag `U`.
pub type RemTags<S, T, U> = <S as repr::Split<T, U>>::RemainderTags;

/// The type list calculated by substituting type list `S` with type `T` and its
/// index tag `U`.
pub type Substitute<S, T, T2, U> = <S as repr::Split<T, U>>::Substitute<T2>;

impl<S: repr::SumList> Sum<S> {
    /// Returns the value if the `Sum` is inhabited with the specified type.
    ///
    /// Otherwise, returns a `Sum` of its remainder types.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// assert_eq!(s.try_unwrap::<i32, _>(), Ok(42i32));
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(236u64);
    /// assert_eq!(
    ///     s.try_unwrap::<i32, _>(),
    ///     Err(<Sum![u64, String]>::new(236u64))
    /// );
    /// ```
    pub fn try_unwrap<T, U>(self) -> Result<T, Sum<Rem<S, T, U>>>
    where
        S: repr::Split<T, U>,
        U: Tag,
    {
        let mut this = ManuallyDrop::new(self);
        match S::try_unwrap(this.tag) {
            Ok(()) => Ok(unsafe { S::into_data_unchecked(ManuallyDrop::take(&mut this.data)) }),
            Err(tag) => unsafe {
                let data = mem::transmute_copy(&this.data);
                Err(Sum { tag, data })
            },
        }
    }

    /// Performs the given function if the `Sum` is inhabited with the specified
    /// type.
    ///
    /// This function returns a `Sum` of a list of new types, in which the
    /// specified type is replaced with the result type of the function.
    ///
    /// This function can be called in chain.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// let s: Sum![u8, u64, usize] = s
    ///     .map(|value: i32| (value + 1) as u8)
    ///     .map(|s: String| s.len());
    /// assert_eq!(s.get(), Some(&43u8));
    /// ```
    pub fn map<T, T2, U>(self, f: impl FnOnce(T) -> T2) -> Sum<Substitute<S, T, T2, U>>
    where
        S: repr::Split<T, U>,
        U: Tag,
    {
        let mut this = ManuallyDrop::new(self);
        let tag = this.tag;
        match S::try_unwrap(tag) {
            Ok(()) => {
                let data = f(unsafe { S::into_data_unchecked(ManuallyDrop::take(&mut this.data)) });
                let data = <Substitute<S, T, T2, U> as repr::Split<T2, U>>::from_data(data);
                Sum {
                    tag,
                    data: ManuallyDrop::new(data),
                }
            }
            Err(_) => unsafe {
                let data = mem::transmute_copy(&this.data);
                Sum { tag, data }
            },
        }
    }
}

/// The remainder type list from splitting type list `S` with type list `S2` and
/// its index tag map `UMap`.
pub type NarrowRem<S, S2, UMap> = <S as repr::SplitList<S2, UMap>>::Remainder;

impl<S: repr::SumList> Sum<S> {
    /// Returns a `Sum` of specified list of type narrowed from the callee's
    /// type list if the `Sum` is inhabited within the specified type list.
    ///
    /// Otherwise, returns a `Sum` of its remainder types.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::{Sum, T};
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// assert_eq!(s.narrow::<T![i32, u64], _>(), Ok(<Sum![i32, u64]>::new(42i32)));
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(236u64);
    /// assert_eq!(s.narrow::<T![i32, String], _>(), Err(236u64.into()));
    /// ```
    pub fn narrow<S2, UMap>(self) -> Result<Sum<S2>, Sum<NarrowRem<S, S2, UMap>>>
    where
        S: repr::SplitList<S2, UMap>,
        S2: repr::SumList,
    {
        let this = ManuallyDrop::new(self);
        match <S as repr::SplitList<S2, UMap>>::narrow_tag(this.tag) {
            Ok(tag) => unsafe {
                let data = mem::transmute_copy(&this.data);
                Ok(Sum { tag, data })
            },
            Err(tag) => unsafe {
                let data = mem::transmute_copy(&this.data);
                Err(Sum { tag, data })
            },
        }
    }

    /// Returns a `Sum` of specified list of type broadened from the callee's
    /// type list.
    ///
    /// Unlike [`Sum::narrow`], this function always succeed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::{Sum, T};
    ///
    /// let s: Sum![i32, u64] = Sum::new(42i32);
    /// assert_eq!(
    ///     s.broaden::<T![i32, u64, String], _>(),
    ///     <Sum![i32, u64, String]>::new(42i32)
    /// );
    /// ```
    pub fn broaden<S2, UMap>(self) -> Sum<S2>
    where
        S2: repr::SplitList<S, UMap>,
    {
        unsafe {
            let tag = <S2 as repr::SplitList<S, UMap>>::broaden_tag(self.tag);
            let mut data = MaybeUninit::<S2::Repr>::uninit();
            data.as_mut_ptr()
                .cast::<ManuallyDrop<S::Repr>>()
                .write(ptr::read(&self.data));

            mem::forget(self);
            let data = data.assume_init();

            Sum {
                tag,
                data: ManuallyDrop::new(data),
            }
        }
    }
}

impl<S: derive::SumDebug> fmt::Debug for Sum<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", unsafe { S::debug(&self.data, self.tag) })
    }
}

impl<S: derive::SumDisplay> fmt::Display for Sum<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { S::display(&self.data, self.tag) })
    }
}

impl<S: repr::SumList> Drop for Sum<S> {
    fn drop(&mut self) {
        unsafe { S::drop(&mut self.data, self.tag) }
    }
}

impl<S: derive::SumClone> Clone for Sum<S> {
    fn clone(&self) -> Self {
        Sum {
            tag: self.tag,
            data: unsafe { S::clone(&self.data, self.tag) },
        }
    }
}

impl<S: derive::SumPartialEq> PartialEq for Sum<S> {
    fn eq(&self, other: &Self) -> bool {
        self.tag == other.tag && unsafe { S::eq(&self.data, &other.data, self.tag) }
    }
}

impl<S: derive::SumPartialEq + Eq> Eq for Sum<S> {}

impl<S: derive::SumPartialOrd> PartialOrd for Sum<S> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.tag.cmp(&other.tag) {
            core::cmp::Ordering::Equal => unsafe {
                S::partial_cmp(&self.data, &other.data, self.tag)
            },
            other => Some(other),
        }
    }
}

impl<S: derive::SumOrd + Eq> Ord for Sum<S> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.tag
            .cmp(&other.tag)
            .then_with(|| unsafe { S::cmp(&self.data, &other.data, self.tag) })
    }
}

impl<S: derive::SumHash> Hash for Sum<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
        unsafe { S::hash(&self.data, self.tag, state) }
    }
}

#[cfg(test)]
mod tests {
    use std::string::{String, ToString};

    use super::*;
    use crate::tag::*;

    #[test]
    fn basic() {
        type T0 = (u32, ());
        type T1 = (u32, (String, ()));
        type T2 = (u32, (String, (u32, ())));

        let sum: Sum<T0> = 12345.into();
        assert_eq!(sum.get(), Some(&12345));

        let mut sum: Sum<T1> = sum.broaden();
        assert_eq!(sum.get::<u32, _>(), Some(&12345));
        assert_eq!(sum.get::<_, U1>(), None);

        sum = Sum::new("Hello World!".to_string());
        assert_eq!(sum.get(), Some(&"Hello World!".to_string()));

        let sum: Sum<T2> = sum.broaden::<_, T![U2, U1]>();
        assert_eq!(sum.get(), Some(&"Hello World!".to_string()));

        let sum: Sum<T1> = sum.narrow::<_, T![U0, U0]>().unwrap();
        let sum: Sum<(String, ())> = sum.narrow::<T0, _>().unwrap_err();
        assert_eq!(*sum, "Hello World!");
    }
}
