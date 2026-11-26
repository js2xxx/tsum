use typenum::{Bit, IsEqual, Unsigned};

/// A type that can be stored in a [`Union`](super::Union).
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

/// Compares the element IDs of `Self` and `F`. Use [`Eq`](tyalias@Eq) to name
/// the result or `ElemEq<F, Output = typenum::B1>` to require matching IDs in a
/// bound.
pub trait ElemEq<F> {
    /// [`typenum::B1`] for equal IDs, or [`typenum::B0`] otherwise.
    type Output: Bit;
}
/// The result of comparing the element IDs of `F` and `G`.
///
/// # Examples
///
/// ```
/// use tsum::union::Eq;
/// use typenum::Bit;
///
/// assert!(Eq::<bool, bool>::to_bool());
/// assert!(!Eq::<bool, u32>::to_bool());
/// ```
pub type Eq<F, G> = <F as ElemEq<G>>::Output;

impl<E, F> ElemEq<F> for E
where
    E: Element,
    F: Element<Id: typenum::IsEqual<E::Id>>,
{
    type Output = typenum::Eq<F::Id, E::Id>;
}

/// Tests whether a list contains the ID of `E`. Use [`Contains`] to name the
/// result or [`UnionOf`](super::UnionOf) to access a value of type `E`.
pub trait ElemContains<E> {
    /// [`typenum::B1`] when the ID occurs in the list, or [`typenum::B0`]
    /// otherwise.
    type Output: Bit;
}
/// The membership bit for the ID of `E` in `L`. It depends only on the member
/// list, regardless of which value a union currently holds.
///
/// # Examples
///
/// ```
/// use tsum::{T, union::Contains};
/// use typenum::Bit;
///
/// type Members = T![char, bool];
/// assert!(Contains::<bool, Members>::to_bool());
/// assert!(!Contains::<u32, Members>::to_bool());
/// ```
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

/// A list of [elements](Element) with distinct IDs. Write it with
/// [`T!`](macro@crate::T) and use [`Insert`] or [`Merge`] to combine lists.
/// Use [`UnionList`](super::UnionList) when declaring a generic union value.
pub trait ElementList {}

impl ElementList for () {}

impl<Head, Tail> ElementList for (Head, Tail)
where
    Head: Element,
    Tail: ElementList + ElemContains<Head, Output = typenum::B0>,
{
}

/// Adds `E` at the front if its ID is absent. Use `L: ElemInsert<E>` in a
/// generic bound and [`Insert<L, E>`](Insert) to name the resulting list.
pub trait ElemInsert<E: Element, Cond = !>: ElementList {
    /// The resulting list, which contains the ID of `E` once.
    type Output: ElementList;
}
/// The list obtained by prepending `E` to `L` if its ID is absent.
/// Inserting an existing member preserves its position.
///
/// # Examples
///
/// ```
/// use tsum::{T, Union, union::Insert};
///
/// type Members = T![bool, char];
/// let first: Union<Insert<Members, u32>> = Union::new(7u32);
/// let _: Union![u32, bool, char] = first;
/// let same: Union<Insert<Members, char>> = Union::new('a');
/// let _: Union![bool, char] = same;
/// ```
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

/// Combines two lists of elements. Use `L: ElemMerge<R>` in a generic
/// bound and [`Merge<L, R>`](Merge) to name the resulting list.
pub trait ElemMerge<L2: ElementList>: ElementList {
    /// The merged list. Newly inserted members appear in reverse order before
    /// `Self`.
    type Output: ElementList;
}
/// The list obtained by [merging](ElemMerge) `L2` into `L1`.
///
/// # Examples
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
mod impls {
    use typenum::*;

    use super::*;

    macro_rules! trivial_impl {
        (@IMP $t:ty, $i:literal) => {
            unsafe impl Element for $t {
                type Id = ${concat(U, $i)};
            }
        };
        ($($t:ty),* $(,)?) => {
            $(trivial_impl!(@IMP $t, ${index()});)*
        };
    }

    trivial_impl! {
        i8, i16, i32, i64, i128, isize,
        u8, u16, u32, u64, u128, usize,
        f32, f64,
        bool, char, &str,
        !, (),
    }
}
