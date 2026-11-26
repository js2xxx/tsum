use typenum::{B0, B1};

use super::{Contains, ElemContains, Element, ElementList, Index, UnionOf, UnsignedList};

/// The members shared by two lists, in the order they appear in the left list.
///
/// Each output member has a zero-based position in each original list. An ID
/// shared by the lists must identify the same Rust type on both sides.
///
/// # Examples
///
/// ```
/// use core::marker::PhantomData;
/// use tsum::{T, union::ElemIntersect};
/// use typenum::{U0, U2};
///
/// type Left = T![bool, char, u8];
/// type Right = T![u8, i32, bool];
/// let _: PhantomData<T![bool, u8]> = PhantomData::<<Left as ElemIntersect<Right>>::Output>;
/// let _: PhantomData<T![U0, U2]> = PhantomData::<<Left as ElemIntersect<Right>>::LhsIndices>;
/// let _: PhantomData<T![U2, U0]> = PhantomData::<<Left as ElemIntersect<Right>>::RhsIndices>;
/// ```
///
/// Two instantiations of the same derived generic type share an element ID.
/// Using different instantiations on opposite sides prevents the intersection
/// from being formed, even if the lists also share other members.
///
/// ```compile_fail
/// use tsum::{T, union::{ElemIntersect, Element, ElementList}};
///
/// #[derive(Element)]
/// struct Slot<T>(T);
///
/// fn intersect<L: ElemIntersect<R>, R: ElementList>() {}
/// intersect::<T![bool, Slot<u8>], T![Slot<u16>, bool]>();
/// ```
pub trait ElemIntersect<L2: ElementList>:
    ElementList + SharedMembers<L2, Shared = Self::Output>
{
    /// The shared member types.
    type Output: ElementList
        + IndicesIn<Self, Indices = Self::LhsIndices>
        + IndicesIn<L2, Indices = Self::RhsIndices>;
    /// The positions of the output members in `Self`.
    type LhsIndices: UnsignedList;
    /// The positions of the output members in `L2`.
    type RhsIndices: UnsignedList;
}

impl<L, R> ElemIntersect<R> for L
where
    L: ElementList + SharedMembers<R>,
    R: ElementList,
    L::Shared: IndicesIn<L> + IndicesIn<R>,
{
    type Output = L::Shared;
    type LhsIndices = <L::Shared as IndicesIn<L>>::Indices;
    type RhsIndices = <L::Shared as IndicesIn<R>>::Indices;
}

// Select candidates by ID. IndicesIn then requires UnionOf<T> on both lists,
// which proves exact Rust type equality for each candidate.
pub trait SharedMembers<R> {
    type Shared: ElementList;
}

impl<R> SharedMembers<R> for () {
    type Shared = ();
}

impl<Head, Tail, R> SharedMembers<R> for (Head, Tail)
where
    R: ElemContains<Head>,
    Tail: SharedMembers<R>,
    Contains<Head, R>: Include<Head, Tail::Shared>,
{
    type Shared = <Contains<Head, R> as Include<Head, Tail::Shared>>::List;
}

pub trait Include<Head, Tail> {
    type List: ElementList;
}

impl<Head, Tail: ElementList> Include<Head, Tail> for B0 {
    type List = Tail;
}

impl<Head, Tail> Include<Head, Tail> for B1
where
    (Head, Tail): ElementList,
{
    type List = (Head, Tail);
}

pub trait IndicesIn<L: ?Sized> {
    type Indices: UnsignedList;
}

impl<L> IndicesIn<L> for () {
    type Indices = ();
}

impl<Head, Tail, L> IndicesIn<L> for (Head, Tail)
where
    Head: Element,
    L: UnionOf<Head>,
    Tail: IndicesIn<L>,
{
    type Indices = (Index<L, Head>, Tail::Indices);
}
