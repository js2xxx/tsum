//! The TRUE generic sum & union types for Rust.

#![no_std]
#![deny(future_incompatible)]
#![deny(rust_2018_idioms)]
#![deny(rust_2024_compatibility)]
#![allow(edition_2024_expr_fragment_specifier)]
#![warn(missing_docs)]

#[cfg(test)]
extern crate std;

mod macros;
pub mod sum;

pub use tsum_macros::match_sum;

pub use self::sum::Sum;
