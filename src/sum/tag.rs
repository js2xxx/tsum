//! Discriminant storage selected from the maximum member index.

use core::{
    hash::Hash,
    panic::{RefUnwindSafe, UnwindSafe},
};

use super::index::{UInt, UTerm};

pub trait Tag: Copy + Ord + Hash + Send + Sync + Unpin + RefUnwindSafe + UnwindSafe {
    fn from_index(index: usize) -> Self;
    fn index(self) -> usize;
}

impl Tag for () {
    fn from_index(index: usize) {
        assert_eq!(index, 0);
    }

    fn index(self) -> usize {
        0
    }
}

impl Tag for u8 {
    fn from_index(index: usize) -> Self {
        u8::try_from(index).expect("member index must fit the stored tag")
    }

    fn index(self) -> usize {
        usize::from(self)
    }
}

impl Tag for usize {
    fn from_index(index: usize) -> Self {
        index
    }

    fn index(self) -> usize {
        self
    }
}

// Classify the existing unary count without imposing additional bounds on
// generic callers. At index zero there is only one possible value. For a
// positive index, bits above the low byte determine whether u8 suffices.
pub trait TagForIndex {
    type Storage: Tag;
    // After shifting away eight bits, zero selects u8 and any remainder selects
    // usize.
    type ByteIfZero: Tag;
    type Half: TagForIndex;
    type CeilHalf: TagForIndex;
}

type Half<N> = <N as TagForIndex>::Half;
type ShiftRight4<N> = Half<Half<Half<Half<N>>>>;
type AboveByte<N> = ShiftRight4<ShiftRight4<N>>;

impl TagForIndex for UTerm {
    type Storage = ();
    type ByteIfZero = u8;
    type Half = Self;
    type CeilHalf = Self;
}

impl<N: TagForIndex> TagForIndex for UInt<N> {
    type Storage = <AboveByte<Self> as TagForIndex>::ByteIfZero;
    type ByteIfZero = usize;
    // Halving a successor swaps the rounding direction.
    type Half = N::CeilHalf;
    type CeilHalf = UInt<N::Half>;
}
