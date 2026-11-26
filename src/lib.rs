//! Values that hold one member of a list of Rust types.
//!
//! Use [`Sum!`](macro@Sum) for ordered variants, including repeated types.
//! Use [`Union!`](macro@Union) for distinct [`Element`](trait@union::Element)
//! types that you want to select by type alone. Construct a value with `new`,
//! borrow its active member with `get`, or consume it with [`match_sum!`]
//! or [`match_union!`].
//!
//! # Examples
//!
//! ```
//! use tsum::{Sum, Union};
//!
//! let message: Sum![String, u32] = Sum::new(String::from("ready"));
//! assert_eq!(message.get::<String, _>().map(String::as_str), Some("ready"));
//!
//! let setting: Union![bool, u32] = Union::new(3u32);
//! assert_eq!(setting.try_unwrap::<u32>(), Ok(3));
//! ```

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

/// Consumes a [`Sum`](struct@Sum) and returns the result of the first matching
/// arm. Use a struct pattern to name a member type or a suffixed numeric
/// literal such as `42u32`. Put guards on typed arms. Use a final,
/// unconditional `_` if any member is covered only by literals or guards.
///
/// # Examples
///
/// ```
/// use tsum::{Sum, match_sum};
///
/// struct Label(String);
/// let value: Sum![u32, Label] = Sum::new(Label(String::from("ready")));
/// let text = match_sum!(match value {
///     0u32 => String::from("zero"),
///     Label(text) => text,
///     _ => String::from("other number"),
/// });
/// assert_eq!(text, "ready");
/// ```
pub use tsum_macros::match_sum;
/// Consumes a [`Union`](struct@Union) and returns the result of the first
/// matching arm. Use a member's struct pattern or a typed literal to select
/// it. Put guards on typed arms and use a final, unconditional `_` to handle
/// the rest.
///
/// # Examples
///
/// ```
/// use tsum::{Union, match_union, union::Element};
///
/// #[derive(Element)]
/// struct Port(u16);
///
/// let value: Union![Port, bool] = Union::new(Port(443));
/// let name = match_union!(match value {
///     Port(port) if port == 443 => "https",
///     Port(_) => "other port",
///     _ => "flag",
/// });
/// assert_eq!(name, "https");
/// ```
pub use tsum_macros::match_union;

pub use self::{sum::Sum, union::Union};
