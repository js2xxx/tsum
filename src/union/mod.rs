//! The generic union type for Rust.
//!
//! Unlike [sum types], each member of a [`Union`] implements [`Element`] and
//! has a distinct element ID. Use [`Union!`] to write the list of members.
//!
//! ```
//! use tsum::{T, Union};
//!
//! let mut value: Union![u32, bool, char] = Union::new('a');
//! *value.get_mut::<char>().unwrap() = 'b';
//! assert_eq!(value.get::<bool>(), None);
//! let subset = value.narrow::<T![char, u32]>().unwrap();
//! let full: Union![bool, u32, char] = subset.broaden();
//! assert_eq!(full.try_unwrap::<char>(), Ok('b'));
//! ```
//!
//! [sum types]: crate::sum::Sum
//! [`Union!`]: macro@crate::Union

use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    pin::Pin,
};

use crate::sum::Sum;

mod derive;
mod elem;
mod repr;

/// Makes a local struct, enum, or union a member type by implementing
/// [`Element`](trait@self::Element). If the `tsum` dependency has another name,
/// use `#[tsum(crate = path)]` to specify its path.
///
/// # Examples
///
/// ```
/// use tsum as choices;
/// use choices::{Union, union::Element};
///
/// #[derive(Element, Debug, PartialEq)]
/// #[tsum(crate = choices)]
/// struct Port(u16);
///
/// let value: Union![bool, Port] = Union::new(Port(443));
/// assert_eq!(value.get::<Port>(), Some(&Port(443)));
/// ```
pub use tsum_macros::Element;

pub use self::{
    elem::*,
    repr::{UnionList, UnionOf, UnionOfList},
};

/// A tagged value containing one member of the [union list](UnionList) `L`.
///
/// Cloning and formatting use the active value. Comparisons order different
/// members by their positions in `L`. Hashing includes the position and value.
/// Each trait is available when all members implement it.
///
/// # Examples
///
/// ```
/// use tsum::Union;
///
/// let value: Union![u32, bool] = Union::new(42u32);
/// assert_eq!(value.clone().get(), Some(&42u32));
/// assert!(value < Union::new(false));
/// ```
///
/// A repeated element ID makes the list invalid.
///
/// ```compile_fail
/// use tsum::Union;
///
/// let _: Union![u8, u8] = Union::new(1u8);
/// ```
pub struct Union<L: UnionList>(Sum<L::Members>);

impl Union<()> {
    /// Instantiates a never type from an empty `Union`.
    ///
    /// This is useful for marking out branches of code that are unreachable
    /// at compile time without using [`unreachable!`] or sorts.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let flag: Union![bool] = true.into();
    /// let flag = flag.try_unwrap::<bool>().unwrap_or_else(|empty| empty.unreachable());
    /// assert!(flag);
    /// ```
    pub fn unreachable(self) -> ! {
        self.0.unreachable()
    }
}

impl<T: Element> From<T> for Union<(T, ())> {
    /// Wraps a value in a single-member union.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let flag: Union![bool] = true.into();
    /// assert!(*flag);
    /// ```
    fn from(value: T) -> Self {
        Self(value.into())
    }
}

impl<T: Element> Deref for Union<(T, ())> {
    type Target = T;

    /// Borrows the only member of a single-member union.
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Element> DerefMut for Union<(T, ())> {
    /// Mutably borrows the only member of a single-member union.
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: Element> Union<(T, ())> {
    /// Moves the only member out of a single-member union.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let mut value: Union![i32] = 3.into();
    /// *value += 1;
    /// assert_eq!(value.into_inner(), 4);
    /// ```
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

/// The zero-based position of the member with `T`'s ID in `L`.
/// Read it as a number with [`typenum::Unsigned`].
///
/// # Examples
///
/// ```
/// use tsum::{T, union::Index};
/// use typenum::Unsigned;
///
/// type Members = T![char, bool];
/// assert_eq!(Index::<Members, bool>::USIZE, 1);
/// ```
pub type Index<L, T> = <L as repr::UnionOfImp<T, !>>::Index;
/// The list in the error returned by [`Union::try_unwrap`]. Removing `T`
/// from `L` preserves the order of the remaining members.
pub type Rem<L, T> = <L as repr::UnionOfImp<T, !>>::Remainder;
/// The list in the error returned by [`Union::narrow`]. It contains the
/// members of `L` outside `L2`, in their original order.
pub type ListRem<L, L2> = <L as repr::UnionOfListImp<L2>>::Remainder;

impl<L: UnionList> Union<L> {
    /// Constructs a union with `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// type Setting = Union![u32, bool];
    /// let value = Setting::new(42u32);
    /// assert_eq!(value.get::<u32>(), Some(&42));
    /// ```
    pub fn new<T: Element>(value: T) -> Self
    where
        L: UnionOf<T>,
    {
        Self(Sum::new::<T, L::Tag>(value))
    }

    /// Constructs a new `Union` from the given value and a marker of its type
    /// lists.
    ///
    /// This is useful when the type information is not known at macro
    /// expansion. It can be used in pairs with [`Union::type_marker`].
    pub fn new_marked<T: Element>(value: T, _: PhantomData<L>) -> Self
    where
        L: UnionOf<T>,
    {
        Self::new(value)
    }

    /// Returns a marker of the type list of the `Union`.
    ///
    /// This is useful when the type information is not known at macro
    /// expansion. It can be used in pairs with [`Union::new_marked`].
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![u32, bool] = Union::new(true);
    /// let marker = value.type_marker();
    /// let number = Union::new_marked(7u32, marker);
    /// assert_eq!(number.get::<u32>(), Some(&7));
    /// ```
    pub fn type_marker(&self) -> PhantomData<L> {
        PhantomData
    }

    /// Returns an immutable reference to the value if the `Union` is inhabited
    /// with the specified type.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![u32, bool] = Union::new(true);
    /// assert_eq!(value.get::<bool>(), Some(&true));
    /// assert_eq!(value.get::<u32>(), None);
    /// ```
    pub fn get<T: Element>(&self) -> Option<&T>
    where
        L: UnionOf<T>,
    {
        self.0.get::<T, L::Tag>()
    }

    /// Returns a mutable reference to the value if the `Union` is inhabited
    /// with the specified type.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let mut value: Union![u32, bool] = Union::new(7u32);
    /// *value.get_mut::<u32>().unwrap() += 1;
    /// assert_eq!(value.get::<u32>(), Some(&8));
    /// ```
    pub fn get_mut<T: Element>(&mut self) -> Option<&mut T>
    where
        L: UnionOf<T>,
    {
        self.0.get_mut::<T, L::Tag>()
    }

    /// Returns a pinned mutable reference to the value if the `Union` is
    /// inhabited with the specified type.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::{marker::PhantomPinned, pin::pin};
    /// use tsum::{Union, union::Element};
    ///
    /// #[derive(Element)]
    /// struct Pinned(PhantomPinned);
    ///
    /// let value: Union![Pinned, bool] = Union::new(Pinned(PhantomPinned));
    /// let mut value = pin!(value);
    /// assert!(value.as_mut().get_pin_mut::<bool>().is_none());
    /// assert!(value.as_mut().get_pin_mut::<Pinned>().is_some());
    /// ```
    pub fn get_pin_mut<T: Element>(self: Pin<&mut Self>) -> Option<Pin<&mut T>>
    where
        L: UnionOf<T>,
    {
        // SAFETY: `Union` is a newtype wrapper around `Sum`, so the `Pin`
        // guarantees are preserved.
        unsafe { self.map_unchecked_mut(|t| &mut t.0) }.get_pin_mut::<T, L::Tag>()
    }

    /// Performs the given function if the `Union` is inhabited with the
    /// specified type.
    ///
    /// This function can be called in chain.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![u32, bool] = Union::new(true);
    /// let mut seen = false;
    /// let value = value.inspect(|flag: &bool| seen = *flag);
    /// assert!(seen);
    /// assert_eq!(value.get::<bool>(), Some(&true));
    /// ```
    pub fn inspect<T: Element, F>(self, f: F) -> Self
    where
        L: UnionOf<T>,
        F: FnOnce(&T),
    {
        Self(self.0.inspect::<T, L::Tag, _>(f))
    }

    /// Performs the given function if the `Union` is inhabited with the
    /// specified type.
    ///
    /// This function can be called in chain.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![u32, char] = Union::new(3u32);
    /// let value = value
    ///     .inspect_mut(|n: &mut u32| *n += 1)
    ///     .inspect(|n: &u32| assert_eq!(*n, 4));
    /// assert_eq!(value.get::<u32>(), Some(&4));
    /// ```
    pub fn inspect_mut<T: Element, F>(self, f: F) -> Self
    where
        L: UnionOf<T>,
        F: FnOnce(&mut T),
    {
        Self(self.0.inspect_mut::<T, L::Tag, _>(f))
    }

    /// Returns the value if the `Union` is inhabited with the specified type.
    ///
    /// Otherwise, returns a `Union` of [its remainder types](Rem).
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![bool, i32] = Union::new(7i32);
    /// let other: Union![i32] = value.try_unwrap::<bool>().unwrap_err();
    /// assert_eq!(other.try_unwrap::<i32>(), Ok(7));
    /// ```
    pub fn try_unwrap<T: Element>(self) -> Result<T, Union<Rem<L, T>>>
    where
        L: UnionOf<T>,
    {
        self.0.try_unwrap::<T, L::Tag>().map_err(Union)
    }

    /// Returns a `Union` of specified list of type narrowed from the callee's
    /// type list if the `Union` is inhabited within the specified type list.
    ///
    /// Otherwise, returns a `Union` of [its remainder types](ListRem).
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::{T, Union};
    ///
    /// let value: Union![bool, i32, char] = Union::new(7i32);
    /// let other: Union![i32] = value.narrow::<T![char, bool]>().unwrap_err();
    /// assert_eq!(*other, 7);
    /// ```
    pub fn narrow<L2>(self) -> Result<Union<L2>, Union<ListRem<L, L2>>>
    where
        L: UnionOfList<L2>,
        L2: UnionList,
    {
        self.0
            .narrow::<L2::Members, L::Map>()
            .map(Union)
            .map_err(Union)
    }

    /// Returns a `Union` of specified list of type broadened from the callee's
    /// type list.
    ///
    /// Unlike [`Union::narrow`], this function always succeed.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![char, u32] = Union::new('a');
    /// let wider: Union![u32, bool, char] = value.broaden();
    /// assert_eq!(wider.get::<char>(), Some(&'a'));
    /// ```
    pub fn broaden<L2>(self) -> Union<L2>
    where
        L2: UnionOfList<L>,
    {
        Union(self.0.broaden::<L2::Members, L2::Map>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        type T0 = (u32, ());
        type T1 = (u32, (&'static str, ()));
        type T2 = (u32, (&'static str, (char, ())));

        let union: Union<T0> = 12345.into();
        assert_eq!(union.get(), Some(&12345u32));

        let mut union: Union<T1> = union.broaden();
        assert_eq!(union.get::<u32>(), Some(&12345));
        assert_eq!(union.get::<&str>(), None);

        union = Union::new("Hello World!");
        assert_eq!(union.get(), Some(&"Hello World!"));

        let union: Union<T2> = union.broaden::<_>();
        assert_eq!(union.get(), Some(&"Hello World!"));

        let union: Union<T1> = union.narrow::<_>().unwrap_or_else(|_| panic!());
        let union: Union<(&str, ())> = union.try_unwrap::<u32>().unwrap_err();
        assert_eq!(*union, "Hello World!");
    }
}
