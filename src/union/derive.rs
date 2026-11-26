use core::{
    any::{Any, TypeId},
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
};

use super::{Union, UnionList};
use crate::sum::{Sum, derive::TypeMeta};

impl<L: UnionList<Members: TypeMeta>> Union<L> {
    /// Returns the [`TypeId`] of the active member.
    pub fn type_id(&self) -> TypeId
    where
        L::Members: 'static,
    {
        self.0.type_id()
    }

    /// Returns the type name of the active member.
    pub fn type_name(&self) -> &'static str {
        self.0.type_name()
    }

    /// Borrows the active value as [`Any`] for downcasting.
    pub fn as_any(&self) -> &dyn Any
    where
        L::Members: 'static,
    {
        self.0.as_any()
    }

    /// Mutably borrows the active value as [`Any`] for downcasting.
    ///
    /// ```
    /// use core::any::TypeId;
    /// use tsum::Union;
    ///
    /// let mut value: Union![bool, u32] = Union::new(7u32);
    /// assert_eq!(value.type_name(), "u32");
    /// assert_eq!(value.type_id(), TypeId::of::<u32>());
    /// *value.as_mut_any().downcast_mut::<u32>().unwrap() += 1;
    /// assert_eq!(value.as_any().downcast_ref::<u32>(), Some(&8));
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
