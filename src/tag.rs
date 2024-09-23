//! Index tags used by [the sum type].
//!
//! # Examples
//!
//! ```rust
//! use tsum::{Sum, T, tag::*};
//!
//! type T0 = T![u32];
//! type T1 = T![u32, String];
//! type T2 = T![u32, String, u32];
//!
//! let sum: Sum<T1> = Sum::new("Hello World!".to_string());
//! assert_eq!(sum.get(), Some(&"Hello World!".to_string()));
//!
//! let sum: Sum<T2> = sum.broaden::<_, T![U2, U1]>();
//! assert_eq!(sum.get(), Some(&"Hello World!".to_string()));
//!
//! let sum: Sum<T1> = sum.narrow::<_, T![U0, U0]>().unwrap();
//! let sum: Sum<(String, ())> = sum.narrow::<T0, _>().unwrap_err();
//! assert_eq!(*sum, "Hello World!");
//! ```
//!
//! [the sum type]: struct@crate::Sum
#![allow(missing_docs)]

use core::marker::PhantomData;

/// The terminator tag used by [the sum type].
/// 
/// See the [module-level documentation] for more.
/// 
/// [the sum type]: struct@crate::Sum
/// [module-level documentation]: self
pub struct UTerm;

/// The accumulator tag used by [the sum type].
/// 
/// See the [module-level documentation] for more.
/// 
/// [the sum type]: struct@crate::Sum
/// [module-level documentation]: self
pub struct UInt<U>(PhantomData<U>);

/// Index tags used by [the sum type].
/// 
/// See the [module-level documentation] for more.
/// 
/// [the sum type]: struct@crate::Sum
/// [module-level documentation]: self
pub trait Tag {
    /// The reified value of the tag.
    const VALUE: u8;
}

impl Tag for UTerm {
    const VALUE: u8 = 0;
}

impl<U: Tag> Tag for UInt<U> {
    const VALUE: u8 = 1 + U::VALUE;
}

pub type U0 = UTerm;
pub type U1 = UInt<U0>;
pub type U2 = UInt<U1>;
pub type U3 = UInt<U2>;
pub type U4 = UInt<U3>;
pub type U5 = UInt<U4>;
pub type U6 = UInt<U5>;
pub type U7 = UInt<U6>;
pub type U8 = UInt<U7>;
pub type U9 = UInt<U8>;

pub type U10 = UInt<U9>;
pub type U11 = UInt<U10>;
pub type U12 = UInt<U11>;
