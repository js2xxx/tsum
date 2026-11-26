//! The TRUE generic sum & union types for Rust.

#![no_std]
#![deny(future_incompatible)]
#![deny(rust_2018_idioms)]
#![deny(rust_2024_compatibility)]
#![allow(edition_2024_expr_fragment_specifier)]
#![warn(missing_docs)]

#[cfg(test)]
extern crate std;

#[doc(hidden)]
pub mod exports {
    pub use typenum;
}

mod macros;
mod private;
pub mod sum;
pub mod union;

/// Matches a [`Sum`](struct@Sum) by its active member and a pattern for its
/// value.
///
/// # Examples
///
/// ```rust
/// use tsum::{Sum, T, match_sum};
///
/// type MySum = Sum![u32, String, f64];
/// let sum: MySum = Sum::new(42u32);
/// let result = match_sum!(match sum {
///     0u32 => "zero",
///     42u32 => "the answer",
///     s @ String { .. } => "a string",
///     123f64 => "a float",
///     _ => "other",
/// });
/// assert_eq!(result, "the answer");
/// ```
pub use tsum_macros::match_sum;
/// Matches a [`Union`](struct@Union) by its active member and a pattern for its
/// value.
///
/// ```
/// use tsum::{Union, match_union};
///
/// let value: Union![u32, bool] = Union::new(42u32);
/// let answer = match_union!(match value {
///     42u32 => "forty-two",
///     _ => "other",
/// });
/// assert_eq!(answer, "forty-two");
/// ```
pub use tsum_macros::match_union;

pub use self::{sum::Sum, union::Union};
