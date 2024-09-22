# THE true generic sum type for Rust

This crate provides THE true generic [sum types](https://en.wikipedia.org/wiki/Tagged_union) in Rust.

The provided sum type are not derived from user-defined types, nor from massive amount of generated `enum`s. Instead, there is only one "true generic sum type" defined in the crate, which uses varadic type lists for type binding.

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

### Common traits

Various common traits are provided for sum types:

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

- Due to the limitation of Rust, `Sum` does not implement `Copy`.
- This crate heavily relies on unsafe code (manually implemented tagged unions). Use it at your own risk.

## License

Licensed under either of
- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.