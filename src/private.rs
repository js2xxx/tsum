use crate::sum::{
    Rem,
    index::{Index, UInt, UTerm},
    repr::{Split, SplitList, SumList},
};

pub trait Sealed {}

impl Sealed for () {}
impl<Head, Tail: Sealed> Sealed for (Head, Tail) {}

// A downstream trait argument can be local even when Self is a tuple.
// Seal the whole relation that each public split implementation handles.
pub trait SealedSplit<T, U> {}

impl<Head, Tail: SumList> SealedSplit<Head, UTerm> for (Head, Tail) {}
impl<Head, Tail: Split<T, U>, T, U: Index> SealedSplit<T, UInt<U>> for (Head, Tail) {}

pub trait SealedSplitList<L, UMap> {}

impl<S: SumList> SealedSplitList<(), ()> for S {}
impl<S, Head, Tail, U, UMap> SealedSplitList<(Head, Tail), (U, UMap)> for S
where
    S: Split<Head, U>,
    Tail: SumList,
    U: Index,
    Rem<S, Head, U>: SplitList<Tail, UMap>,
{
}
