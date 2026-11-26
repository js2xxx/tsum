use typenum::{B0, B1, U0, Unsigned};

use super::elem::{ElemContains, ElemEq, Element, ElementList, Eq};
use crate::{
    private::Sealed,
    sum::{
        index::{Index, UInt, UTerm},
        repr::{Split, SplitList, SumList},
    },
};

/// A tuple list of distinct [elements](Element) with tagged union storage.
///
/// This trait is sealed to `()` and `(Head, Tail)` with a `UnionList` tail
/// whose members have IDs distinct from `Head`.
pub trait UnionList: ElementList + Sealed {
    /// The positional sum list used for storage and tag dispatch.
    #[doc(hidden)]
    type Members: SumList;

    /// The number of members in the list.
    const LEN: usize;
}

type Members<L> = <L as UnionList>::Members;

impl UnionList for () {
    type Members = ();
    const LEN: usize = 0;
}

impl<Head, Tail> UnionList for (Head, Tail)
where
    Head: Element,
    Tail: UnionList + ElemContains<Head, Output = B0>,
{
    type Members = (Head, Tail::Members);
    const LEN: usize = Tail::LEN + 1;
}

/// A union list containing the element `E`.
pub trait UnionOf<E: Element>: UnionOfImp<E, !, Output = E> {}
impl<E: Element, L> UnionOf<E> for L where L: UnionOfImp<E, !, Output = E> {}

// ID comparison locates a candidate. UnionOf additionally requires Rust type
// equality with Output before any operation can use the candidate's index.
pub trait UnionOfImp<E: Element, Cond>
where
    Self: UnionList<Members: Split<Self::Output, Self::Tag, Remainder = Members<Self::Remainder>>>,
{
    type Index: Unsigned;
    type Tag: Index;
    type Output: Element;
    type Remainder: UnionList;
}

impl<T: Element, Head: Element, Tail> UnionOfImp<T, !> for (Head, Tail)
where
    Head: ElemEq<T>,
    Self: UnionOfImp<T, Eq<Head, T>>,
{
    type Index = <Self as UnionOfImp<T, Eq<Head, T>>>::Index;
    type Tag = <Self as UnionOfImp<T, Eq<Head, T>>>::Tag;
    type Output = <Self as UnionOfImp<T, Eq<Head, T>>>::Output;
    type Remainder = <Self as UnionOfImp<T, Eq<Head, T>>>::Remainder;
}

impl<T: Element, Head: Element, Tail> UnionOfImp<T, B1> for (Head, Tail)
where
    Tail: UnionList + ElemContains<Head, Output = B0>,
{
    type Index = U0;
    type Tag = UTerm;
    type Output = Head;
    type Remainder = Tail;
}

impl<T: Element, Head: Element, Tail> UnionOfImp<T, B0> for (Head, Tail)
where
    Tail: ElemContains<Head, Output = B0>
        + UnionOfImp<
            T,
            !,
            Index: core::ops::Add<B1, Output: Unsigned>,
            Remainder: ElemContains<Head, Output = B0>,
        >,
{
    type Index = typenum::Sum<Tail::Index, B1>;
    type Tag = UInt<Tail::Tag>;
    type Output = <Tail as UnionOfImp<T, !>>::Output;
    type Remainder = (Head, Tail::Remainder);
}

/// A union list containing all members of `L`, in any order.
pub trait UnionOfList<L: UnionList>: UnionOfListImp<L, Output = L> {}
impl<L: UnionList, R> UnionOfList<L> for R where R: UnionOfListImp<L, Output = L> {}

pub trait UnsignedList: Sealed {}
impl UnsignedList for () {}
impl<Head: Unsigned, Tail: UnsignedList> UnsignedList for (Head, Tail) {}

pub trait UnionOfListImp<L: UnionList>
where
    Self: UnionList<
        Members: SplitList<Members<Self::Output>, Self::Map, Remainder = Members<Self::Remainder>>,
    >,
{
    type Indices: UnsignedList;
    type Map;
    type Output: UnionList;
    type Remainder: UnionList;
}

impl<L: UnionList> UnionOfListImp<()> for L {
    type Indices = ();
    type Map = ();
    type Output = ();
    type Remainder = L;
}

impl<SupHead, SupTail, SubHead, SubTail> UnionOfListImp<(SubHead, SubTail)> for (SupHead, SupTail)
where
    SupHead: Element,
    SupTail: UnionList + ElemContains<SupHead, Output = B0>,
    SubHead: Element,
    SubTail: UnionList + ElemContains<SubHead, Output = B0>,
    Self: UnionList<Members = (SupHead, SupTail::Members)>
        + UnionOfImp<
            SubHead,
            !,
            Remainder: UnionOfListImp<
                SubTail,
                Output: ElemContains<<Self as UnionOfImp<SubHead, !>>::Output, Output = B0>,
            >,
        >,
{
    type Indices = (
        <Self as UnionOfImp<SubHead, !>>::Index,
        <<Self as UnionOfImp<SubHead, !>>::Remainder as UnionOfListImp<SubTail>>::Indices,
    );
    type Map = (
        <Self as UnionOfImp<SubHead, !>>::Tag,
        <<Self as UnionOfImp<SubHead, !>>::Remainder as UnionOfListImp<SubTail>>::Map,
    );
    type Output = (
        <Self as UnionOfImp<SubHead, !>>::Output,
        <<Self as UnionOfImp<SubHead, !>>::Remainder as UnionOfListImp<SubTail>>::Output,
    );
    type Remainder =
        <<Self as UnionOfImp<SubHead, !>>::Remainder as UnionOfListImp<SubTail>>::Remainder;
}
