use core::{
    any::{Any, TypeId},
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    pin::Pin,
};

use super::{ElemIntersect, Element, Union, UnionList, UnionOf};
use crate::sum::{self, Sum, derive::TypeMeta};

impl<L: UnionList<Members: TypeMeta>> Union<L> {
    /// Returns the type ID of the inhabited value.
    ///
    /// The result of this function is different of calling [`TypeId::of`],
    /// which returns the type ID of the `Union` type itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::any::TypeId;
    /// use tsum::Union;
    ///
    /// let value: Union![u32, bool] = Union::new(true);
    /// assert_eq!(value.type_id(), TypeId::of::<bool>());
    /// ```
    pub fn type_id(&self) -> TypeId
    where
        L::Members: 'static,
    {
        self.0.type_id()
    }

    /// Returns the name of the type of the inhabited value.
    ///
    /// The result of this function is different of calling
    /// [`core::any::type_name`], which returns the type name of the `Union`
    /// type itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![u32, bool] = Union::new(true);
    /// assert_eq!(value.type_name(), core::any::type_name::<bool>());
    /// ```
    pub fn type_name(&self) -> &'static str {
        self.0.type_name()
    }

    /// Coerces the reference of the inhabited value immutably into the dynamic
    /// type.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let value: Union![u32, bool] = Union::new(true);
    /// assert_eq!(value.as_any().downcast_ref::<bool>(), Some(&true));
    /// assert_eq!(value.as_any().downcast_ref::<u32>(), None);
    /// ```
    pub fn as_any(&self) -> &dyn Any
    where
        L::Members: 'static,
    {
        self.0.as_any()
    }

    /// Coerces the reference of the inhabited value mutably into the dynamic
    /// type.
    ///
    /// # Examples
    ///
    /// ```
    /// use tsum::Union;
    ///
    /// let mut value: Union![bool, u32] = Union::new(7u32);
    /// *value.as_mut_any().downcast_mut::<u32>().unwrap() += 1;
    /// assert_eq!(value.get::<u32>(), Some(&8));
    /// ```
    pub fn as_mut_any(&mut self) -> &mut dyn Any
    where
        L::Members: 'static,
    {
        self.0.as_mut_any()
    }
}

impl<L: UnionList> Clone for Union<L>
where
    Sum<L::Members>: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<L: UnionList> fmt::Debug for Union<L>
where
    Sum<L::Members>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<L: UnionList> fmt::Display for Union<L>
where
    Sum<L::Members>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

trait MemberEq<L: UnionList, R: UnionList> {
    fn member_eq(lhs: &Union<L>, rhs: &Union<R>) -> bool;
}

impl<L: UnionList, R: UnionList> MemberEq<L, R> for () {
    fn member_eq(_: &Union<L>, _: &Union<R>) -> bool {
        false
    }
}

impl<Head, Tail, L, R> MemberEq<L, R> for (Head, Tail)
where
    Head: Element + PartialEq,
    Tail: MemberEq<L, R>,
    L: UnionOf<Head>,
    R: UnionOf<Head>,
{
    fn member_eq(lhs: &Union<L>, rhs: &Union<R>) -> bool {
        match lhs.get::<Head>() {
            Some(left) => rhs.get::<Head>().is_some_and(|right| left == right),
            None => Tail::member_eq(lhs, rhs),
        }
    }
}

/// Compares the active values when both unions hold the same member type.
/// Only members shared by the two lists must implement [`PartialEq`].
impl<L, R> PartialEq<Union<R>> for Union<L>
where
    L: UnionList + ElemIntersect<R>,
    R: UnionList,
    L::Output: MemberEq<L, R>,
{
    fn eq(&self, rhs: &Union<R>) -> bool {
        L::Output::member_eq(self, rhs)
    }
}

impl<L: UnionList + Eq> Eq for Union<L> where Self: PartialEq {}

trait MemberOrd<L: UnionList, R: UnionList>: MemberEq<L, R> {
    fn member_cmp(lhs: &Union<L>, rhs: &Union<R>) -> Option<Ordering>;
}

impl<L: UnionList, R: UnionList> MemberOrd<L, R> for () {
    fn member_cmp(_: &Union<L>, _: &Union<R>) -> Option<Ordering> {
        None
    }
}

impl<Head, Tail, L, R> MemberOrd<L, R> for (Head, Tail)
where
    Head: Element + PartialOrd,
    Tail: MemberOrd<L, R>,
    L: UnionOf<Head>,
    R: UnionOf<Head>,
{
    fn member_cmp(lhs: &Union<L>, rhs: &Union<R>) -> Option<Ordering> {
        match lhs.get::<Head>() {
            Some(left) => rhs.get::<Head>().and_then(|right| left.partial_cmp(right)),
            None => Tail::member_cmp(lhs, rhs),
        }
    }
}

impl<L, R> PartialOrd<Union<R>> for Union<L>
where
    L: UnionList + ElemIntersect<R>,
    R: UnionList,
    L::Output: MemberOrd<L, R>,
{
    fn partial_cmp(&self, rhs: &Union<R>) -> Option<Ordering> {
        L::Output::member_cmp(self, rhs)
    }
}

impl<L: UnionList> Hash for Union<L>
where
    L::Members: sum::derive::SumHash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash_data(state);
    }
}

impl<L: UnionList> Iterator for Union<L>
where
    Sum<L::Members>: Iterator,
{
    type Item = <Sum<L::Members> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<L: UnionList> ExactSizeIterator for Union<L>
where
    Sum<L::Members>: ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<L: UnionList> FusedIterator for Union<L> where Sum<L::Members>: FusedIterator {}

impl<L: UnionList> DoubleEndedIterator for Union<L>
where
    Sum<L::Members>: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<L: UnionList> Future for Union<L>
where
    Sum<L::Members>: Future,
{
    type Output = <Sum<L::Members> as Future>::Output;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        unsafe { self.map_unchecked_mut(|t| &mut t.0) }.poll(cx)
    }
}

impl<L: UnionList> core::error::Error for Union<L>
where
    Sum<L::Members>: core::error::Error,
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        self.0.source()
    }
}
