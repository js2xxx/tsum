//! Tagged unions whose members are selected by type.
//!
//! Each member of a [`Union`] implements [`Element`] and has a distinct
//! element ID. Use [`crate::Union!`] to write the list of members. Positions
//! are zero-based and use an eight-bit tag.
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

use core::ops::{Deref, DerefMut};

use crate::sum::Sum;

mod derive;
mod elem;
mod repr;

/// Derives [`Element`](trait@self::Element) for a local struct, enum, or union.
///
/// The generated ID is opaque. The optional `#[tsum(crate = path)]` attribute
/// supplies the path to `typenum` used to spell that ID.
///
/// ```
/// use tsum::{Union, union::Element};
///
/// #[derive(Element, Debug, PartialEq)]
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
    /// Eliminates an empty union, which has no possible values.
    pub fn unreachable(self) -> ! {
        self.0.unreachable()
    }
}

impl<T: Element> From<T> for Union<(T, ())> {
    /// Wraps a value in a single-member union.
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

/// The zero-based position of the member with `T`'s ID in `L`, as a
/// [`typenum::Unsigned`].
pub type Index<L, T> = <L as repr::UnionOfImp<T, !>>::Index;
/// The list obtained by removing `T` from `L`, preserving the remaining order.
pub type Rem<L, T> = <L as repr::UnionOfImp<T, !>>::Remainder;
/// The members of `L` left after removing every member of `L2`, in their
/// original order.
pub type ListRem<L, L2> = <L as repr::UnionOfListImp<L2>>::Remainder;

impl<L: UnionList> Union<L> {
    /// Constructs a union with `T` as its active member.
    pub fn new<T: Element>(value: T) -> Self
    where
        L: UnionOf<T>,
    {
        Self(Sum::new::<T, L::Tag>(value))
    }

    /// Borrows the value if `T` is active.
    pub fn get<T: Element>(&self) -> Option<&T>
    where
        L: UnionOf<T>,
    {
        self.0.get::<T, L::Tag>()
    }

    /// Mutably borrows the value if `T` is active.
    pub fn get_mut<T: Element>(&mut self) -> Option<&mut T>
    where
        L: UnionOf<T>,
    {
        self.0.get_mut::<T, L::Tag>()
    }

    /// Calls `f` with a reference if `T` is active, then returns the union.
    pub fn inspect<T: Element, F>(self, f: F) -> Self
    where
        L: UnionOf<T>,
        F: FnOnce(&T),
    {
        Self(self.0.inspect::<T, L::Tag, _>(f))
    }

    /// Calls `f` with a mutable reference if `T` is active, then returns the
    /// union.
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

    /// Moves out the value if `T` is active. Otherwise returns the union of the
    /// [remaining members](Rem).
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

    /// Moves the value into `L2` if it belongs there, or into the [remaining
    /// list](ListRem) otherwise. The members of `L2` may appear in any order.
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

    /// Moves the value into a list containing all members of `L` in any order.
    /// See [`Union::narrow`] for the inverse operation.
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
