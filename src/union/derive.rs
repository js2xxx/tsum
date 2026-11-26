use core::{
    any::{Any, TypeId},
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    pin::Pin,
};

use super::{Union, UnionList};
use crate::sum::{Sum, derive::TypeMeta};

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

impl<L: UnionList> PartialEq for Union<L>
where
    Sum<L::Members>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<L: UnionList> Eq for Union<L> where Sum<L::Members>: Eq {}

impl<L: UnionList> PartialOrd for Union<L>
where
    Sum<L::Members>: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<L: UnionList> Ord for Union<L>
where
    Sum<L::Members>: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<L: UnionList> Hash for Union<L>
where
    Sum<L::Members>: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
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
