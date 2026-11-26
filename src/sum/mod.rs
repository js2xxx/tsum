//! The generic sum type for Rust.
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

use core::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr,
};

pub(crate) mod derive;
pub mod index;
pub mod repr;
mod tag;
use self::{index::Index, tag::Tag};

/// A value of one member of the ordered type list `S`.
///
/// Each occurrence is a distinct variant, even when two members have the same
/// Rust type. Use [`Sum!`](macro@crate::Sum) to write a concrete type, or use
/// [`SumList`](repr::SumList) as a bound for a generic list.
///
/// Cloning and formatting use the active value. Comparisons order different
/// variants by position and compare values within a variant. Hashing includes
/// the position and value. Each operation requires the corresponding trait on
/// all members.
///
/// A nonempty sum of iterators with the same item type implements [`Iterator`].
/// It also supports double-ended, exact-size, and fused iteration when all
/// members do. A nonempty sum of futures with the same output type can be
/// awaited to obtain that output.
///
/// # Examples
///
/// ```
/// use tsum::Sum;
///
/// type Message = Sum![String, u32];
/// let message = Message::new(String::from("ready"));
/// assert_eq!(message.get::<String, _>().map(String::as_str), Some("ready"));
/// assert_eq!(message.get::<u32, _>(), None);
/// ```
pub struct Sum<S: repr::SumList> {
    tag: S::Discriminant,
    data: ManuallyDrop<S::Repr>,
}

impl<T> From<T> for Sum<(T, ())> {
    /// Wraps a value in a single-member sum.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Sum;
    ///
    /// let value: Sum![String] = String::from("ready").into();
    /// assert_eq!(value.as_str(), "ready");
    /// ```
    fn from(value: T) -> Self {
        Sum::new(value)
    }
}

impl<T> Deref for Sum<(T, ())> {
    type Target = T;

    /// Borrows the only member of a single-member sum.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Sum;
    ///
    /// let value: Sum![i32] = 42.into();
    /// assert_eq!(*value, 42);
    /// ```
    fn deref(&self) -> &Self::Target {
        unsafe { &self.data.data }
    }
}

impl<T> DerefMut for Sum<(T, ())> {
    /// Mutably borrows the only member of a single-member sum.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Sum;
    ///
    /// let mut value: Sum![i32] = 42.into();
    /// *value += 1;
    /// assert_eq!(*value, 43);
    /// ```
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut self.data.data }
    }
}

impl<T> Sum<(T, ())> {
    /// Consumes a single-member sum and returns its value.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Sum;
    ///
    /// let value: Sum![String] = String::from("ready").into();
    /// let text: String = value.into_inner();
    /// assert_eq!(text, "ready");
    /// ```
    pub fn into_inner(self) -> T {
        let mut this = ManuallyDrop::new(self);
        // A singleton always has its head initialized.
        unsafe { ManuallyDrop::take(&mut this.data.data) }
    }
}

impl Sum<()> {
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
        S::type_id(self.tag.index())
    }

    /// Returns the name of the type of the inhabited value.
    ///
    /// The result of this function is different of calling
    /// [`core::any::type_name`], which returns the type name of the `Sum` type
    /// itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Sum;
    ///
    /// let value: Sum![u32, bool] = Sum::new(true);
    /// assert_eq!(value.type_name(), core::any::type_name::<bool>());
    /// ```
    pub fn type_name(&self) -> &'static str
    where
        S: derive::TypeMeta,
    {
        S::type_name(self.tag.index())
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
    /// ```
    pub fn as_any(&self) -> &dyn core::any::Any
    where
        S: derive::TypeMeta + 'static,
    {
        unsafe { S::as_any(&self.data, self.tag.index()) }
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
        unsafe { S::as_mut_any(&mut self.data, self.tag.index()) }
    }
}

impl<S: repr::SumList> Sum<S> {
    /// Constructs the sum with `value` at position `U`.
    ///
    /// The index can be inferred when `T` occurs once. Specify it when several
    /// members have the same type `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::{Sum, sum::index::U1};
    ///
    /// let value = <Sum![u32, u32]>::new::<_, U1>(42u32);
    /// assert_eq!(value.get::<u32, U1>(), Some(&42));
    /// ```
    pub fn new<T, U>(value: T) -> Self
    where
        S: repr::SumOf<T, U>,
        U: Index,
    {
        Sum {
            tag: S::Discriminant::from_index(U::TAG),
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
        S: repr::SumOf<T, U>,
        U: Index,
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
        S: repr::SumOf<T, U>,
        U: Index,
    {
        (self.tag.index() == U::TAG).then(|| unsafe { &*S::as_ptr(&raw const *self.data) })
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
        S: repr::SumOf<T, U>,
        U: Index,
    {
        (self.tag.index() == U::TAG)
            .then(|| unsafe { &mut *S::as_ptr(&raw mut *self.data).cast_mut() })
    }

    /// Returns a pinned mutable reference to the value if the `Sum` is
    /// inhabited with the specified type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tsum::Sum;
    ///
    /// let s: Sum![i32, u64, String] = Sum::new(42i32);
    /// let s = core::pin::pin!(s);
    /// assert_eq!(
    ///     s.get_pin_mut::<i32, _>(),
    ///     Some(core::pin::Pin::new(&mut 42i32))
    /// );
    /// ```
    pub fn get_pin_mut<T, U>(self: Pin<&mut Self>) -> Option<Pin<&mut T>>
    where
        S: repr::SumOf<T, U>,
        U: Index,
    {
        (self.tag.index() == U::TAG).then(|| unsafe {
            let data = &raw mut *self.get_unchecked_mut().data;
            Pin::new_unchecked(&mut *S::as_ptr(data).cast_mut())
        })
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
        S: repr::SumOf<T, U>,
        U: Index,
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
        S: repr::SumOf<T, U>,
        U: Index,
        F: FnOnce(&mut T),
    {
        if let Some(value) = self.get_mut() {
            f(value);
        }
        self
    }
}

/// The members of `S` left after removing `T` at position `U`, in their
/// original order. Use `Sum<Rem<S, T, U>>` to name the error from
/// [`Sum::try_unwrap`].
pub type Rem<S, T, U> = <S as repr::SumOf<T, U>>::Remainder;

/// The index map for broadening [`Rem<S, T, U>`](Rem) back into `S`. Use it
/// to restore the original positions when the list contains repeated types.
///
/// # Examples
///
/// ```
/// use tsum::{Sum, T, sum::{RemTags, index::{U0, U1}}};
///
/// type Pair = T![u8, u8];
/// let value = Sum::<Pair>::new::<_, U1>(7u8);
/// let remaining = value.try_unwrap::<u8, U0>().unwrap_err();
/// let restored = remaining.broaden::<Pair, RemTags<Pair, u8, U0>>();
/// assert_eq!(restored.get::<u8, U1>(), Some(&7));
/// ```
pub type RemTags<S, T, U> = <S as repr::SumOf<T, U>>::RemainderTags;

/// The member list of the sum returned by [`Sum::map`]. The occurrence of `T`
/// at `U` becomes `T2` and all other positions are preserved.
pub type Substitute<S, T, T2, U> = <S as repr::SumOf<T, U>>::Substitute<T2>;

impl<S: repr::SumList> Sum<S> {
    /// Returns the value if the `Sum` is inhabited with the specified type.
    ///
    /// Otherwise, returns a `Sum` of [its remainder types](Rem).
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
        S: repr::SumOf<T, U>,
        U: Index,
    {
        match S::try_unwrap(self.tag.index()) {
            Ok(()) => {
                let mut this = ManuallyDrop::new(self);
                Ok(unsafe { S::into_data_unchecked(ManuallyDrop::take(&mut this.data)) })
            }
            // The remainder contains the active member at the adjusted tag.
            Err(tag) => Err(unsafe { self.retag(tag) }),
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
        S: repr::SumOf<T, U>,
        U: Index,
    {
        let tag = self.tag.index();
        match S::try_unwrap(tag) {
            Ok(()) => {
                let mut this = ManuallyDrop::new(self);
                let data = f(unsafe { S::into_data_unchecked(ManuallyDrop::take(&mut this.data)) });
                let data = <Substitute<S, T, T2, U> as repr::SumOf<T2, U>>::from_data(data);
                Sum {
                    tag: Tag::from_index(tag),
                    data: ManuallyDrop::new(data),
                }
            }
            // Only an inactive member changed type. Its replacement can have
            // a different size or alignment.
            Err(_) => unsafe { self.retag(tag) },
        }
    }
}

/// The member list in the `Err` branch of [`Sum::narrow`]. It contains the
/// members of `S` left after selecting `S2` with `UMap`, in their original
/// order.
pub type ListRem<S, S2, UMap> = <S as repr::SumOfList<S2, UMap>>::Remainder;

impl<S: repr::SumList> Sum<S> {
    /// Returns a `Sum` of specified list of type narrowed from the callee's
    /// type list if the `Sum` is inhabited within the specified type list.
    ///
    /// Otherwise, returns a `Sum` of [its remainder types](ListRem).
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
    pub fn narrow<S2, UMap>(self) -> Result<Sum<S2>, Sum<ListRem<S, S2, UMap>>>
    where
        S: repr::SumOfList<S2, UMap>,
        S2: repr::SumList,
    {
        // Both tags designate the original active member in their respective
        // lists.
        match <S as repr::SumOfList<S2, UMap>>::narrow_tag(self.tag.index()) {
            Ok(tag) => Ok(unsafe { self.retag(tag) }),
            Err(tag) => Err(unsafe { self.retag(tag) }),
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
        S2: repr::SumOfList<S, UMap>,
    {
        let tag = <S2 as repr::SumOfList<S, UMap>>::broaden_tag(self.tag.index());
        // The mapped tag selects the same member in the superset.
        unsafe { self.retag(tag) }
    }

    // SAFETY: `tag` must select the exact type of the active value in S2.
    unsafe fn retag<S2: repr::SumList>(self, tag: usize) -> Sum<S2> {
        let tag = S2::Discriminant::from_index(tag);
        let this = ManuallyDrop::new(self);
        let mut data = MaybeUninit::<S2::Repr>::uninit();
        // Both representations store the member at offset zero. The smaller
        // size covers the entire value, including any of its padding. A byte
        // copy preserves uninitialized bytes and pointer provenance.
        let count = size_of::<S::Repr>().min(size_of::<S2::Repr>());
        unsafe {
            ptr::copy_nonoverlapping(
                ptr::from_ref(&this.data).cast::<u8>(),
                data.as_mut_ptr().cast::<u8>(),
                count,
            );
            Sum {
                tag,
                data: ManuallyDrop::new(data.assume_init()),
            }
        }
    }
}

impl<S: derive::SumDebug> fmt::Debug for Sum<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(unsafe { S::debug(&self.data, self.tag.index()) }, f)
    }
}

impl<S: derive::SumDisplay> fmt::Display for Sum<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(unsafe { S::display(&self.data, self.tag.index()) }, f)
    }
}

impl<S: repr::SumList> Drop for Sum<S> {
    fn drop(&mut self) {
        unsafe { S::drop(&mut self.data, self.tag.index()) }
    }
}

impl<S: derive::SumClone> Clone for Sum<S> {
    fn clone(&self) -> Self {
        Sum {
            tag: self.tag,
            data: unsafe { S::clone(&self.data, self.tag.index()) },
        }
    }
}

impl<S: derive::SumPartialEq> PartialEq for Sum<S> {
    fn eq(&self, other: &Self) -> bool {
        self.tag == other.tag && unsafe { S::eq(&self.data, &other.data, self.tag.index()) }
    }
}

impl<S: derive::SumPartialEq + Eq> Eq for Sum<S> {}

impl<S: derive::SumPartialOrd> PartialOrd for Sum<S> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.tag.cmp(&other.tag) {
            core::cmp::Ordering::Equal => unsafe {
                S::partial_cmp(&self.data, &other.data, self.tag.index())
            },
            other => Some(other),
        }
    }
}

impl<S: derive::SumOrd + Eq> Ord for Sum<S> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.tag
            .cmp(&other.tag)
            .then_with(|| unsafe { S::cmp(&self.data, &other.data, self.tag.index()) })
    }
}

impl<S: derive::SumHash> Hash for Sum<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Preserve the zero tag in the hash of a singleton even though its
        // discriminant takes no space in memory.
        if size_of::<S::Discriminant>() == 0 {
            0u8.hash(state);
        } else {
            self.tag.hash(state);
        }
        unsafe { S::hash(&self.data, self.tag.index(), state) }
    }
}

/// Iterates over the active member, yielding the item type shared by all
/// members.
///
/// # Examples
///
/// ```
/// use tsum::Sum;
///
/// type Numbers = Sum![core::ops::Range<u8>, core::iter::Once<u8>];
/// let mut numbers = Numbers::new(1u8..4);
/// assert_eq!(numbers.next_back(), Some(3));
/// assert_eq!(numbers.collect::<Vec<_>>(), vec![1, 2]);
/// ```
impl<S: derive::SumIterator> Iterator for Sum<S> {
    type Item = S::Item;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe { S::next(&mut self.data, self.tag.index()) }
    }
}

impl<S: derive::SumExactSizeIterator> ExactSizeIterator for Sum<S> {
    fn len(&self) -> usize {
        unsafe { S::len(&self.data, self.tag.index()) }
    }
}

impl<S: derive::SumFusedIterator> core::iter::FusedIterator for Sum<S> {}

impl<S: derive::SumDoubleEndedIterator> DoubleEndedIterator for Sum<S> {
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe { S::next_back(&mut self.data, self.tag.index()) }
    }
}

/// Awaiting the sum polls the active future and yields the output type shared
/// by all members. This lets different branches return different future types.
///
/// # Examples
///
/// ```
/// use core::future::{Pending, Ready, pending, ready};
/// use tsum::Sum;
///
/// async fn answer(available: bool) -> u32 {
///     let response: Sum![Ready<u32>, Pending<u32>] = if available {
///         Sum::new(ready(42))
///     } else {
///         Sum::new(pending::<u32>())
///     };
///     response.await
/// }
/// ```
impl<S: derive::SumFuture> core::future::Future for Sum<S> {
    type Output = S::Output;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };
        unsafe { S::poll(Pin::new_unchecked(&mut this.data), this.tag.index(), cx) }
    }
}

#[cfg(test)]
mod tests {
    use std::string::{String, ToString};

    use super::{index::*, *};
    use crate::T;

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

    #[test]
    fn mapping_an_inactive_member_can_grow_or_shrink_storage() {
        #[repr(align(64))]
        struct Large {
            _payload: [u8; 128],
        }

        let mut number = 7;
        let value: crate::Sum![u8, &mut i32] = Sum::new(&mut number);
        let value: crate::Sum![Large, &mut i32] = value.map(|_: u8| panic!("inactive member"));
        let value: crate::Sum![(), &mut i32] = value.map(|_: Large| panic!("inactive member"));
        *value.try_unwrap::<&mut i32, _>().unwrap() += 1;
        assert_eq!(number, 8);
    }

    #[test]
    #[should_panic(expected = "sum tag exceeds usize")]
    fn inserting_a_member_checks_for_tag_overflow() {
        <(bool, ()) as repr::SumOf<bool, U0>>::from_remainder(usize::MAX);
    }

    #[test]
    fn matching() {
        use crate as tsum;

        struct X1(u32);
        struct X2(u32, String);
        type T2 = (X1, (X2, (u32, ())));

        let sum: Sum<T2> = Sum::new(X1(12345u32));
        let x = tsum_macros::match_sum!(match sum {
            X1(12345) => 0,
            X2(10..=456, s) => {
                std::println!("{s}");
                1
            }
            23456u32 => 3,
            X1(x) | X2(x, ..) => x,
            .. => 4,
        });
        assert_eq!(x, 0);
    }
}
