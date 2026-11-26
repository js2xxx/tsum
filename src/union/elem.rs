use typenum::{Bit, IsEqual, Unsigned};

/// A type with a type-level ID for membership tests in [`Union`](super::Union).
///
/// Use [`#[derive(Element)]`](derive@super::Element) on a local type.
/// Instantiations of the same derived generic type share an ID. A union
/// can contain one such instantiation. Access still requires its exact type.
///
/// ```compile_fail
/// use tsum::{Union, union::Element};
///
/// #[derive(Element)]
/// struct Slot<T>(T);
///
/// let value: Union![Slot<u32>] = Union::new(Slot(42u32));
/// let _ = value.get::<Slot<bool>>();
/// ```
///
/// # Safety
///
/// Use a canonical [`typenum`] unsigned integer for `Id`. Give elements that
/// must coexist in the same union distinct IDs. ID equality is used for set
/// operations. Accessing a value additionally requires an exact Rust type
/// match.
pub unsafe trait Element {
    /// The key used to look up this type in element lists.
    type Id: Unsigned + IsEqual<Output = typenum::B1> + typenum::Cmp<Output = typenum::Equal>;
}

/// Compares the element IDs of `Self` and `F`.
pub trait ElemEq<F> {
    /// [`typenum::B1`] for equal IDs, or [`typenum::B0`] otherwise.
    type Output: Bit;
}
/// The result bit of comparing the IDs of `F` and `G`.
pub type Eq<F, G> = <F as ElemEq<G>>::Output;

impl<E, F> ElemEq<F> for E
where
    E: Element,
    F: Element<Id: typenum::IsEqual<E::Id>>,
{
    type Output = typenum::Eq<F::Id, E::Id>;
}

/// Tests whether an element list contains the ID of `E`.
pub trait ElemContains<E> {
    /// [`typenum::B1`] when the ID occurs in the list, or [`typenum::B0`]
    /// otherwise.
    type Output: Bit;
}
/// The result bit of looking up the ID of `E` in `L`.
pub type Contains<E, L> = <L as ElemContains<E>>::Output;

impl<E> ElemContains<E> for () {
    type Output = typenum::B0;
}

impl<E, Head, Tail> ElemContains<E> for (Head, Tail)
where
    E: ElemEq<Head>,
    Tail: ElemContains<E>,
    Eq<E, Head>: core::ops::BitOr<Tail::Output, Output: Bit>,
{
    type Output = typenum::Or<Eq<E, Head>, Tail::Output>;
}

/// A tuple list of [elements](Element) with pairwise distinct IDs.
///
/// The empty list is `()`. A nonempty list is `(Head, Tail)`, where `Tail`
/// is an element list. Use [`crate::T!`] to spell these lists.
pub trait ElementList {}

impl ElementList for () {}

impl<Head, Tail> ElementList for (Head, Tail)
where
    Head: Element,
    Tail: ElementList + ElemContains<Head, Output = typenum::B0>,
{
}

/// Inserts `E` at the head of a list if its ID is absent.
/// The default `Cond` selects the appropriate case using [`Contains`].
pub trait ElemInsert<E: Element, Cond = !>: ElementList {
    /// The resulting list, which contains the ID of `E` once.
    type Output: ElementList;
}
/// The list obtained by prepending `E` to `L` if its ID is absent.
pub type Insert<L, E> = <L as ElemInsert<E>>::Output;

impl<E, L> ElemInsert<E, !> for L
where
    E: Element,
    L: ElemContains<E> + ElemInsert<E, Contains<E, L>>,
{
    type Output = <L as ElemInsert<E, Contains<E, L>>>::Output;
}

impl<E, L> ElemInsert<E, typenum::B0> for L
where
    E: Element,
    L: ElementList + ElemContains<E, Output = typenum::B0>,
{
    type Output = (E, L);
}

impl<E, L> ElemInsert<E, typenum::B1> for L
where
    E: Element,
    L: ElementList + ElemContains<E, Output = typenum::B1>,
{
    type Output = L;
}

/// Inserts the members of `L2` into `Self`, visiting `L2` from head to tail.
pub trait ElemMerge<L2: ElementList>: ElementList {
    /// The merged list. Newly inserted members appear in reverse order before
    /// `Self`.
    type Output: ElementList;
}
/// The list obtained by [merging](ElemMerge) `L2` into `L1`.
///
/// ```
/// use tsum::{T, Union, union::Merge};
///
/// type Members = Merge<T![bool, char], T![u32, bool, i8]>;
/// let value: Union<Members> = Union::new(true);
/// let _: Union![i8, u32, bool, char] = value;
/// ```
pub type Merge<L1, L2> = <L1 as ElemMerge<L2>>::Output;

impl<L: ElementList> ElemMerge<()> for L {
    type Output = L;
}

impl<L: ElementList, Head, Tail> ElemMerge<(Head, Tail)> for L
where
    Head: Element,
    Tail: ElementList + ElemContains<Head, Output = typenum::B0>,
    L: ElemInsert<Head, Output: ElemMerge<Tail>>,
{
    type Output = Merge<Insert<L, Head>, Tail>;
}

// -------------------------
// Trivial implementations

macro_rules! trivial_impl {
    ($($t:ty => $id:ident),* $(,)?) => {
        $(unsafe impl Element for $t {
            type Id = typenum::$id;
        })*
    };
}

trivial_impl! {
    i8 => U0, i16 => U1, i32 => U2, i64 => U3, isize => U4,
    u8 => U5, u16 => U6, u32 => U7, u64 => U8, usize => U9,
    f32 => U10, f64 => U11,
    bool => U12, char => U13, &str => U14,
    ! => U15, () => U16,
}
