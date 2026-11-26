//! The module dealing with the underlying representation of the [`Sum`] type.
//!
//! # Implementation details
//!
//! This crate defines a sum type by hand-written tagged unions. In other words,
//! the memory layout of a sum type resembles a tagged union:
//!
//! ```rust,no_run
//! # use core::convert::Infallible;
//! # use core::mem::ManuallyDrop;
//!
//! struct Nil(Infallible);
//! union Cons<T, Next> {
//!     data: ManuallyDrop<T>,
//!     next: ManuallyDrop<Next>,
//! }
//!
//! // For example only. Not actually defined.
//! struct RawSum2<T1, T2> {
//!     tag: u8,
//!     data: Cons<T1, Cons<T2, Nil>>,
//! }
//! ```
//!
//! And all the traits are implemented upon this layout.
//!
//! See the source code for more details.
//!
//! [`Sum`]: crate::sum::Sum

use core::{convert::Infallible, mem::ManuallyDrop};

use super::{
    NarrowRem, Rem,
    index::{Index, U1, UInt, UTerm},
};
use crate::private::{Sealed, SealedSplit, SealedSplitList};

/// The terminator type of the underlying union of the [`Sum`] type.
///
/// [`Sum`]: crate::sum::Sum
pub struct Nil(pub(super) Infallible);

/// The accumulator type of the underlying union of the [`Sum`] type.
///
/// [`Sum`]: crate::sum::Sum
#[repr(C)]
pub union Cons<T, U> {
    pub(super) data: ManuallyDrop<T>,
    pub(super) next: ManuallyDrop<U>,
}

/// A tuple list with tagged storage for [`Sum`].
///
/// This trait is sealed to `()` and `(Head, Tail)` with a `SumList` tail.
/// The tag is the zero-based position of the active member. The representation
/// stores that member at offset zero with its required size and alignment.
///
/// [`Sum`]: crate::sum::Sum
pub trait SumList: Count + Sealed {
    /// The underlying representation of the `Sum` type.
    type Repr;

    /// The index tag mapping from the type list to the `Sum` type.
    type Tags<U>;

    /// # Safety
    ///
    /// `this` must own the member selected by `tag`. After the call its storage
    /// must be reinitialized before accessing or dropping the member again.
    #[doc(hidden)]
    unsafe fn drop(this: &mut ManuallyDrop<Self::Repr>, tag: u8);
}

impl SumList for () {
    type Repr = Nil;
    type Tags<U> = ();

    unsafe fn drop(_: &mut ManuallyDrop<Nil>, _: u8) {}
}

impl<Head, Tail> SumList for (Head, Tail)
where
    Tail: SumList,
{
    type Repr = Cons<Head, Tail::Repr>;
    type Tags<U> = (U, Tail::Tags<U>);

    unsafe fn drop(this: &mut ManuallyDrop<Self::Repr>, tag: u8) {
        if tag == 0 {
            unsafe { ManuallyDrop::drop(&mut this.data) };
        } else {
            unsafe { Tail::drop(&mut this.next, tag - 1) }
        }
    }
}

/// A tuple list containing `T` at position `U`.
///
/// This sealed trait preserves the order of the other members when removing
/// or replacing `T`.
pub trait Split<T, U: Index>: SumList + SealedSplit<T, U> {
    #[doc(hidden)]
    fn from_data(data: T) -> Self::Repr;

    /// # Safety
    ///
    /// The active member of `this` must be the one at `U`.
    #[doc(hidden)]
    unsafe fn into_data_unchecked(this: Self::Repr) -> T;

    #[doc(hidden)]
    fn as_ptr(this: &Self::Repr) -> *const T {
        core::ptr::from_ref(this).cast()
    }

    #[doc(hidden)]
    fn as_mut_ptr(this: &mut Self::Repr) -> *mut T {
        core::ptr::from_mut(this).cast()
    }

    /// The remainder type list from splitting type list `Self` with type `T`
    /// and its index tag `U`.
    type Remainder: SumList;

    /// The remainder index tag map from splitting type list `Self` with type
    /// `T` and its index tag `U`.
    type RemainderTags;

    /// The type list calculated by substituting type list `Self` with type `T`
    /// and its index tag `U`.
    type Substitute<T2>: Split<T2, U>;

    #[doc(hidden)]
    fn from_remainder(tag: u8) -> u8;

    #[doc(hidden)]
    fn try_unwrap(tag: u8) -> Result<(), u8>;
}

impl<Head, Tail> Split<Head, UTerm> for (Head, Tail)
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

    fn from_remainder(tag: u8) -> u8 {
        tag.checked_add(1).expect("sum tag exceeds u8")
    }

    fn try_unwrap(tag: u8) -> Result<(), u8> {
        match tag.checked_sub(1) {
            None => Ok(()),
            Some(tag) => Err(tag),
        }
    }
}

impl<Head, Tail, T, U: Index> Split<T, UInt<U>> for (Head, Tail)
where
    Tail: Split<T, U>,
{
    fn from_data(data: T) -> Self::Repr {
        Cons {
            next: ManuallyDrop::new(Tail::from_data(data)),
        }
    }

    unsafe fn into_data_unchecked(this: Self::Repr) -> T {
        unsafe { Tail::into_data_unchecked(ManuallyDrop::into_inner(this.next)) }
    }

    type Remainder = (Head, <Tail as Split<T, U>>::Remainder);
    type RemainderTags = (UTerm, <Tail as Split<T, U>>::RemainderTags);
    type Substitute<T2> = (Head, Tail::Substitute<T2>);

    fn from_remainder(tag: u8) -> u8 {
        if tag < UInt::<U>::TAG {
            tag
        } else {
            tag.checked_add(1).expect("sum tag exceeds u8")
        }
    }

    fn try_unwrap(tag: u8) -> Result<(), u8> {
        let cur = UInt::<U>::TAG;
        match tag.cmp(&cur) {
            core::cmp::Ordering::Equal => Ok(()),
            core::cmp::Ordering::Less => Err(tag),
            core::cmp::Ordering::Greater => Err(tag - 1),
        }
    }
}

/// Counts the number of elements in a type list using index tags.
pub trait Count: Sealed {
    /// The number of elements in the type list, measured by index tags.
    type Count: Index;
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

/// A tuple list that can be partitioned into `TList` and its remainder.
///
/// This sealed trait uses `UList` to identify each selected occurrence,
/// including when `TList` reorders members.
pub trait SplitList<TList: SumList, UList>: SumList + SealedSplitList<TList, UList> {
    /// The remainder type list from splitting type list `Self` with type list
    /// `TList` and its index tag map `UList`.
    type Remainder: SumList;

    #[doc(hidden)]
    fn broaden_tag(tag: u8) -> u8;

    #[doc(hidden)]
    fn narrow_tag(tag: u8) -> Result<u8, u8>;
}

impl<T: SumList> SplitList<(), ()> for T {
    type Remainder = Self;

    fn broaden_tag(tag: u8) -> u8 {
        unreachable!("mapping tag {tag} from an empty set")
    }

    fn narrow_tag(tag: u8) -> Result<u8, u8> {
        Err(tag)
    }
}

impl<SubHead, SubTail, SuperHead, SuperTail, HeadIndex: Index, TailIndex>
    SplitList<(SubHead, SubTail), (HeadIndex, TailIndex)> for (SuperHead, SuperTail)
where
    SubTail: SumList,
    SuperTail: SumList,
    Self: Split<SubHead, HeadIndex>,
    Rem<Self, SubHead, HeadIndex>: SplitList<SubTail, TailIndex>,
{
    type Remainder = NarrowRem<Rem<Self, SubHead, HeadIndex>, SubTail, TailIndex>;

    fn broaden_tag(tag: u8) -> u8 {
        match <(SubHead, SubTail) as Split<SubHead, UTerm>>::try_unwrap(tag) {
            Ok(()) => HeadIndex::TAG,
            Err(remainder) => {
                let ret = Rem::<Self, SubHead, HeadIndex>::broaden_tag(remainder);
                Self::from_remainder(ret)
            }
        }
    }

    fn narrow_tag(tag: u8) -> Result<u8, u8> {
        Ok(match Self::try_unwrap(tag) {
            Ok(()) => 0,
            Err(remainder) => {
                let ret = Rem::<Self, SubHead, HeadIndex>::narrow_tag(remainder)?;
                <(SubHead, SubTail) as Split<SubHead, UTerm>>::from_remainder(ret)
            }
        })
    }
}
