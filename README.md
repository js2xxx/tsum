# THE true generic sum and union types for Rust

[![crates.io](https://img.shields.io/crates/v/tsum.svg)](https://crates.io/crates/tsum)
[![docs.rs](https://docs.rs/tsum/badge.svg)](https://docs.rs/tsum)

`tsum` provides two tagged unions backed by varadic type lists. `Sum![A, B, A]` distinguishes members by position and accepts arbitrary Rust types. `Union![A, B]` selects members by type and requires each member to have a distinct `Element` ID. Both use the same handwritten representation and store one active value inline. [Tagged unions](https://en.wikipedia.org/wiki/Tagged_union)

The representation traits are sealed to varadic type lists. Generic code can use `SumList` and `UnionList` as bounds, and local types can derive `Element` to become union members.

## Wait what? Varadic type lists?

Yes, varadic type lists, or heterogeneous lists in Rust, which is represented by tuple lists:

```rust
// A tuple list of 4 types.
type List1 = (u32, (usize, (String, (Vec<i8>, ()))));
```

In fact, tuple lists are a simplified version of the nil-cons lists, which are used in functional programming languages like Haskell:

```rust
type Cons<T, Next> = (T, Next);
type Nil = ();

// A nil-cons list of 4 types. Equals the definition above.
type List1 = Cons<u32, Cons<usize, Cons<String, Cons<Vec<i8>, Nil>>>>;
```

Using tuple lists can maximize readability while retaining all the advantages of varadic type lists.

## Usage

### Specifying types

Although tuple lists are the most readable way among all the heterogeneous lists, it is still too much verbose to write them manually. Therefore, the crate provides a macro to generate sum types directly:

```rust
use tsum::{Sum, T};

// Create a sum type with 4 types...
type Sum1 = Sum![u32, usize, String, Vec<u8>];

// ...which expands to:
type Sum1Expanded = Sum<T![u32, usize, String, Vec<u8>]>;

// ...which expands again to:
type Sum1ExpandedAgain
    = Sum<(u32, (usize, (String, (Vec<u8>, ()))))>;
```

### Manipulating values

Various mechanisms are provided to manipulate values with sum types:

```rust
# type Sum1 = tsum::Sum![u32, usize, String, Vec<u8>];

// Creating values of sum types is also very easy:
let v1: Sum1 = Sum1::new(1u32);
let mut v2: Sum1 = Sum1::new(2usize);
let v3: Sum1 = Sum1::new("hello".to_string());
let v4: Sum1 = Sum1::new(vec![1, 2, 3]);

// However, accessing the value inside the sum type is
// a bit more complicated:

assert_eq!(v4.get(), Some(&vec![1, 2, 3]));
assert_eq!(v2.get::<u32, _>(), None);
assert_eq!(v2.get_mut::<usize, _>(), Some(&mut 2usize));

// The code below will not compile
// because the type `()` is not a member of `Sum1`.
//
// assert_eq!(v2.get::<(), _>(), None);
```

There are also special methods on `Sum` of one/zero type:

```rust
# use tsum::Sum;

let sum: Sum![u32] = 42u32.into();
assert_eq!(*sum, 42); // Direct dereferencing.
assert_eq!(sum.into_inner(), 42); // Move into its inner value.

let _closure = |sum: Sum![]| -> ! {
    sum.unreachable()
};
// The closure above can compile but cannot be called because
// `Sum![]` is empty, which is uninhabited.
```

### Manipulating type lists

The real power of sum types comes from the ability to manipulate its type lists, such as narrowing, broadening, or replacing types within them:

```rust
use tsum::{Sum, T};

type Sum1 = Sum![u32, usize, String, Vec<u8>];
type Sum2 = Sum![u32, usize, Vec<u8>];
type Sum3 = Sum![u32, usize, i64, Vec<u8>];

let sum: Sum1 = Sum1::new(42u32);

// Broadening or narrowing a sum type is very easy:
let sum: Sum2 = sum.narrow().unwrap();
let sum: Sum3 = sum.broaden();

// Failed operations also shrinks its type list to a subset.
let sum: Sum2 = sum.try_unwrap::<i64, _>().unwrap_err();
let value: u32 = sum.try_unwrap().unwrap();
assert_eq!(value, 42);

let sum: Sum1 = Sum1::new("hello".to_string());
let sum: Sum3 = sum.map(|s: String| s.as_bytes()[0] as i64);
assert_eq!(sum, Sum3::new(104i64));
```

### Unions with distinct member types

Use `Union!` when each type occurs once. The type determines its position, so calls such as `get::<T>()` and `try_unwrap::<T>()` need just the member type. Derive `tsum::union::Element` for a local type to use it alongside built-in elements such as `u32`, `bool`, and `&str`. Generic instantiations of one derived type share an element ID.

```rust
use tsum::{T, Union, union::Element};

#[derive(Element, Debug, PartialEq)]
struct Port(u16);

type Setting = Union![bool, Port, u32];
let mut setting = Setting::new(Port(80));
setting.get_mut::<Port>().unwrap().0 = 443;
assert_eq!(setting.get::<u32>(), None);

// Narrowing accepts a reordered subset. On failure it returns the other members.
let subset: Union![u32, Port] = setting.narrow::<T![u32, Port]>().unwrap();
let setting: Setting = subset.broaden();
let remaining: Union![Port] = setting.narrow::<T![bool, u32]>().unwrap_err();
assert_eq!(remaining.into_inner(), Port(443));
```

`match_union!` matches the active value with the same pattern syntax as `match_sum!`. For type-level set operations, `union::Insert<L, T>` prepends a missing member and `union::Merge<L, R>` inserts each member of `R` into `L` in turn.

### Common traits

Both `Sum` and `Union` implement `Clone`, `Debug`, `Display`, `Eq`, and `Hash` when every member supports the corresponding trait. A `Sum` compares and hashes the active position and value, and orders different members by position. Two unions can be compared across different lists. They are equal when they hold the same member type and the payloads compare equal. Only shared members need `PartialEq`. Use `left.type_eq(&right)` to compare just the active types. A union hashes its active value.

Use `type_name()` to inspect the active type. For lists of `'static` types, `type_id()`, `as_any()`, and `as_mut_any()` also support runtime type inspection.

```rust
use tsum::{Sum, T};

type Sum1 = Sum![u32, usize, String];

fn assert_send_sync<T: Send + Sync>(_: T) {}

assert_send_sync(Sum1::new(42u32));
assert_send_sync(Sum1::new("hello".to_string()));

let sum: Sum1 = Sum::new(42usize);

let cloned = sum.clone();
assert!(sum != Sum::new(42u32));
assert_eq!(format!("{sum}"), "42");
```

## Caveats

- Both types run the active member's destructor, which precludes implementing `Copy`.
- Both types store the discriminant as `()` for zero or one member, `u8` for 2 through 256 members, and `usize` for 257 or more. Deep tuple lists may require a higher `recursion_limit` in the consuming crate.
- Use a wrapper struct to derive custom traits for a particular `Sum` or `Union` type.
- This crate heavily relies on unsafe code (manually implemented tagged unions) and several **nightly** features. Use it at your own risk.

## License

Licensed under either of
- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.
