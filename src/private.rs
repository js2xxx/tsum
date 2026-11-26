use crate::sum::{
    Rem,
    index::{Index, UInt, UTerm},
    repr::{SumList, SumOf, SumOfList},
};

pub trait Sealed {}

impl Sealed for () {}
impl<Head, Tail: Sealed> Sealed for (Head, Tail) {}

// A downstream trait argument can be local even when Self is a tuple.
// Seal the whole relation that each public split implementation handles.
pub trait SealedSumOf<T, U> {}

impl<Head, Tail: SumList> SealedSumOf<Head, UTerm> for (Head, Tail) {}
impl<Head, Tail: SumOf<T, U>, T, U: Index> SealedSumOf<T, UInt<U>> for (Head, Tail) {}

pub trait SealedSumOfList<L, UMap> {}

impl<S: SumList> SealedSumOfList<(), ()> for S {}
impl<S, Head, Tail, U, UMap> SealedSumOfList<(Head, Tail), (U, UMap)> for S
where
    S: SumOf<Head, U>,
    Tail: SumList,
    U: Index,
    Rem<S, Head, U>: SumOfList<Tail, UMap>,
{
}
