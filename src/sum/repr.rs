//! Type-list bounds for generic functions that accept
//! [`Sum`](struct@crate::Sum).
//!
//! Use [`SumList`] for an arbitrary list, [`SumOf`] to require a member at a
//! particular position, and [`SumOfList`] to require a subset.
//!
//! # Examples
//!
//! ```
//! use tsum::{Sum, sum::{index::Index, repr::SumOf}};
//!
//! fn active_number<L, U>(value: &Sum<L>) -> Option<&u32>
//! where
//!     U: Index,
//!     L: SumOf<u32, U>,
//! {
//!     value.get::<u32, U>()
//! }
//!
//! let value: Sum![bool, u32] = Sum::new(7u32);
//! assert_eq!(active_number(&value), Some(&7));
//! ```

use core::{convert::Infallible, mem::ManuallyDrop};

use super::{
    ListRem, Rem,
    index::{Index, U1, UInt, UTerm},
    tag::{Tag, TagForIndex},
};
use crate::private::{Sealed, SealedSumOf, SealedSumOfList};

/// The uninhabited representation of an empty sum. Use `Sum![]` to name the
/// sum itself and [`Sum::unreachable`](crate::Sum::unreachable) to consume it.
pub struct Nil(pub(super) Infallible);

/// The representation of a nonempty sum. To declare and construct a value,
/// use [`Sum!`](macro@crate::Sum) and [`Sum::new`](crate::Sum::new).
#[repr(C)]
pub union Cons<T, U> {
    pub(super) data: ManuallyDrop<T>,
    pub(super) next: ManuallyDrop<U>,
}

/// A valid ordered member list for [`Sum`](struct@crate::Sum).
///
/// Lists use `()` for the empty list and `(Head, Tail)` for a member followed
/// by another list. Write the list itself with [`T!`](macro@crate::T), or use
/// [`Sum!`](macro@crate::Sum) to name the sum containing one of its members.
pub trait SumList: Count + Sealed {
    /// The storage type selected for the active member position.
    type Discriminant: Tag;

    /// The representation associated with the list.
    type Repr;

    /// A tuple list with one copy of `U` for each member, in list order.
    /// For example, a two-member list has `Tags<U> = (U, (U, ()))`.
    type Tags<U>;

    /// # Safety
    ///
    /// `this` must own the member selected by `tag`. After the call its storage
    /// must be reinitialized before accessing or dropping the member again.
    #[doc(hidden)]
    unsafe fn drop(this: &mut ManuallyDrop<Self::Repr>, tag: usize);
}

impl SumList for () {
    type Discriminant = ();
    type Repr = Nil;
    type Tags<U> = ();

    unsafe fn drop(_: &mut ManuallyDrop<Nil>, _: usize) {}
}

impl<Head, Tail> SumList for (Head, Tail)
where
    Tail: SumList,
{
    // The tail length is the largest zero-based position in this list.
    type Discriminant = <Tail::Count as TagForIndex>::Storage;
    type Repr = Cons<Head, Tail::Repr>;
    type Tags<U> = (U, Tail::Tags<U>);

    unsafe fn drop(this: &mut ManuallyDrop<Self::Repr>, tag: usize) {
        if tag == 0 {
            unsafe { ManuallyDrop::drop(&mut this.data) };
        } else {
            unsafe { Tail::drop(&mut this.next, tag - 1) }
        }
    }
}

/// Selects the occurrence of `T` at position `U` in a member list.
///
/// The associated types describe the list after removing that occurrence or
/// replacing it with another type. This trait is sealed and is primarily a
/// bound for generic APIs.
pub trait SumOf<T, U: Index>: SumList + SealedSumOf<T, U> {
    #[doc(hidden)]
    fn from_data(data: T) -> Self::Repr;

    /// # Safety
    ///
    /// The active member of `this` must be the one at `U`.
    #[doc(hidden)]
    unsafe fn into_data_unchecked(this: Self::Repr) -> T;

    #[doc(hidden)]
    fn as_ptr(this: *const Self::Repr) -> *const T {
        this.cast()
    }

    /// The list left after removing the selected occurrence.
    type Remainder: SumList;

    /// The index map for broadening the remainder back into the original list.
    /// See [`RemTags`](crate::sum::RemTags) for an example.
    type RemainderTags;

    /// The list obtained by replacing the selected occurrence with `T2`.
    type Substitute<T2>: SumOf<T2, U>;

    #[doc(hidden)]
    fn from_remainder(tag: usize) -> usize;

    #[doc(hidden)]
    fn try_unwrap(tag: usize) -> Result<(), usize>;
}

impl<Head, Tail> SumOf<Head, UTerm> for (Head, Tail)
where
    Tail: SumList,
{
    fn from_data(data: Head) -> Self::Repr {
        Cons { data: ManuallyDrop::new(data) }
    }

    unsafe fn into_data_unchecked(this: Self::Repr) -> Head {
        unsafe { ManuallyDrop::into_inner(this.data) }
    }

    type Remainder = Tail;
    type RemainderTags = Tail::Tags<U1>;
    type Substitute<T2> = (T2, Tail);

    fn from_remainder(tag: usize) -> usize {
        tag.checked_add(1).expect("sum tag exceeds usize")
    }

    fn try_unwrap(tag: usize) -> Result<(), usize> {
        match tag.checked_sub(1) {
            None => Ok(()),
            Some(tag) => Err(tag),
        }
    }
}

impl<Head, Tail, T, U: Index> SumOf<T, UInt<U>> for (Head, Tail)
where
    Tail: SumOf<T, U>,
{
    fn from_data(data: T) -> Self::Repr {
        Cons {
            next: ManuallyDrop::new(Tail::from_data(data)),
        }
    }

    unsafe fn into_data_unchecked(this: Self::Repr) -> T {
        unsafe { Tail::into_data_unchecked(ManuallyDrop::into_inner(this.next)) }
    }

    type Remainder = (Head, <Tail as SumOf<T, U>>::Remainder);
    type RemainderTags = (UTerm, <Tail as SumOf<T, U>>::RemainderTags);
    type Substitute<T2> = (Head, Tail::Substitute<T2>);

    fn from_remainder(tag: usize) -> usize {
        if tag < UInt::<U>::TAG {
            tag
        } else {
            tag.checked_add(1).expect("sum tag exceeds usize")
        }
    }

    fn try_unwrap(tag: usize) -> Result<(), usize> {
        let cur = UInt::<U>::TAG;
        match tag.cmp(&cur) {
            core::cmp::Ordering::Equal => Ok(()),
            core::cmp::Ordering::Less => Err(tag),
            core::cmp::Ordering::Greater => Err(tag - 1),
        }
    }
}

/// The number of entries in a member list, available as a type.
/// Use [`Index::TAG`] to read its numeric value.
///
/// # Examples
///
/// ```
/// use tsum::{T, sum::{index::Index, repr::Count}};
///
/// type Length = <T![u8, bool, u8] as Count>::Count;
/// assert_eq!(Length::TAG, 3);
/// ```
pub trait Count: Sealed {
    /// The number of members. The empty list has count zero and repeated types
    /// each contribute one.
    type Count: Index + TagForIndex;
}

impl Count for () {
    type Count = UTerm;
}

impl<Head, Tail> Count for (Head, Tail)
where
    Tail: Count,
{
    type Count = UInt<Tail::Count>;
}

/// A list containing every occurrence requested by `TList`. Use this bound
/// for [`Sum::narrow`](crate::Sum::narrow) or
/// [`Sum::broaden`](crate::Sum::broaden).
///
/// Read `UList` from left to right. Each index selects one member from the
/// list **remaining after the previous selections**. Rust infers this map
/// when each selection is unambiguous.
///
/// # Examples
///
/// ```
/// use tsum::{Sum, T, sum::index::{U0, U1, U2}};
///
/// type Source = Sum![u8, bool, u8];
/// let value = Source::new::<_, U2>(9u8);
/// // Select the last u8, then bool at index 1 in the remaining [u8, bool].
/// let selected = value.narrow::<T![u8, bool], T![U2, U1]>().unwrap();
/// assert_eq!(selected.get::<u8, U0>(), Some(&9));
/// ```
pub trait SumOfList<TList: SumList, UList>: SumList + SealedSumOfList<TList, UList> {
    /// The members not selected for `TList`, in their source order.
    type Remainder: SumList;

    #[doc(hidden)]
    fn broaden_tag(tag: usize) -> usize;

    #[doc(hidden)]
    fn narrow_tag(tag: usize) -> Result<usize, usize>;
}

impl<T: SumList> SumOfList<(), ()> for T {
    type Remainder = Self;

    fn broaden_tag(tag: usize) -> usize {
        unreachable!("mapping tag {tag} from an empty set")
    }

    fn narrow_tag(tag: usize) -> Result<usize, usize> {
        Err(tag)
    }
}

impl<SubHead, SubTail, SuperHead, SuperTail, HeadIndex: Index, TailIndex>
    SumOfList<(SubHead, SubTail), (HeadIndex, TailIndex)> for (SuperHead, SuperTail)
where
    SubTail: SumList,
    SuperTail: SumList,
    Self: SumOf<SubHead, HeadIndex>,
    Rem<Self, SubHead, HeadIndex>: SumOfList<SubTail, TailIndex>,
{
    type Remainder = ListRem<Rem<Self, SubHead, HeadIndex>, SubTail, TailIndex>;

    fn broaden_tag(tag: usize) -> usize {
        match <(SubHead, SubTail) as SumOf<SubHead, UTerm>>::try_unwrap(tag) {
            Ok(()) => HeadIndex::TAG,
            Err(remainder) => {
                let ret = Rem::<Self, SubHead, HeadIndex>::broaden_tag(remainder);
                Self::from_remainder(ret)
            }
        }
    }

    fn narrow_tag(tag: usize) -> Result<usize, usize> {
        Ok(match Self::try_unwrap(tag) {
            Ok(()) => 0,
            Err(remainder) => {
                let ret = Rem::<Self, SubHead, HeadIndex>::narrow_tag(remainder)?;
                <(SubHead, SubTail) as SumOf<SubHead, UTerm>>::from_remainder(ret)
            }
        })
    }
}
