//! Zero-based positions for selecting [`Sum`](struct@crate::Sum) members.
//!
//! Use `_` to infer the position of a type that occurs once. When a type occurs
//! more than once, pass its position explicitly. [`U0`] through [`U12`] name
//! the first thirteen positions. Use [`UInt<U>`](UInt) for the position after
//! `U`.
//!
//! # Examples
//!
//! ```
//! use tsum::{Sum, sum::index::{U0, U1}};
//!
//! let value = <Sum![bool, bool]>::new::<_, U1>(true);
//! assert_eq!(value.get::<bool, U0>(), None);
//! assert_eq!(value.get::<bool, U1>(), Some(&true));
//! ```
#![allow(missing_docs)]

use core::marker::PhantomData;

/// Position zero. Use its alias [`U0`] to select the first member.
pub struct UTerm;

/// The position immediately after `U`. For example, `UInt<U12>` selects the
/// member at index 13.
pub struct UInt<U>(PhantomData<U>);

/// A type-level position in an ordered sum. Use this bound for an index
/// parameter passed to [`Sum::get`](crate::Sum::get) or
/// [`Sum::new`](crate::Sum::new).
pub trait Index {
    /// The zero-based member position, as a `usize`.
    const TAG: usize;
}

impl Index for UTerm {
    const TAG: usize = 0;
}

impl<U: Index> Index for UInt<U> {
    const TAG: usize = U::TAG.checked_add(1).expect("sum tag exceeds usize");
}

/// Selects the member at zero-based position 0.
pub type U0 = UTerm;
/// Selects the member at zero-based position 1.
pub type U1 = UInt<U0>;
/// Selects the member at zero-based position 2.
pub type U2 = UInt<U1>;
/// Selects the member at zero-based position 3.
pub type U3 = UInt<U2>;
/// Selects the member at zero-based position 4.
pub type U4 = UInt<U3>;
/// Selects the member at zero-based position 5.
pub type U5 = UInt<U4>;
/// Selects the member at zero-based position 6.
pub type U6 = UInt<U5>;
/// Selects the member at zero-based position 7.
pub type U7 = UInt<U6>;
/// Selects the member at zero-based position 8.
pub type U8 = UInt<U7>;
/// Selects the member at zero-based position 9.
pub type U9 = UInt<U8>;

/// Selects the member at zero-based position 10.
pub type U10 = UInt<U9>;
/// Selects the member at zero-based position 11.
pub type U11 = UInt<U10>;
/// Selects the member at zero-based position 12.
pub type U12 = UInt<U11>;
