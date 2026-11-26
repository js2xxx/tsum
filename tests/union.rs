use core::{
    any::TypeId,
    cell::Cell,
    cmp::Ordering::{Equal, Greater, Less},
    hash::{Hash, Hasher},
};
use std::{collections::hash_map::DefaultHasher, rc::Rc};

use tsum::{T, Union, match_union, union::Element};

fn hash(value: impl Hash) -> u64 {
    let mut state = DefaultHasher::new();
    value.hash(&mut state);
    state.finish()
}

#[test]
fn traits_dispatch_to_the_active_member() {
    type Value = Union![bool, i32];
    let mut value = Value::new(7i32);
    let copy = value.clone();

    assert_eq!(value.type_id(), TypeId::of::<i32>());
    assert_eq!(value.type_name(), "i32");
    assert_eq!(value.as_any().downcast_ref::<i32>(), Some(&7));
    *value.as_mut_any().downcast_mut::<i32>().unwrap() = 9;
    assert_eq!(format!("{copy:04}"), "0007");
    assert_eq!(format!("{value:?}"), "9");
    assert_eq!(hash(&value), hash(9i32));
    assert_eq!(hash(Value::new(true)), hash(true));
    let reordered: Union![i32, bool] = Union::new(9i32);
    assert_eq!(value, reordered);
    assert_eq!(hash(&value), hash(&reordered));
}

#[test]
fn equality_across_overlapping_lists() {
    #[derive(Debug, Element)]
    struct LeftOnly;
    #[derive(Debug, Element)]
    struct RightOnly;

    type Left<'a> = Union![LeftOnly, &'a str, u8];
    type Right<'a> = Union![u8, RightOnly, &'a str];

    let text = String::from("shared");
    let lhs = Left::new(text.as_str());
    let rhs = Right::new("shared");
    assert!(lhs.type_eq(&rhs));
    assert_eq!(lhs, rhs);
    assert_eq!(rhs, lhs);
    assert_ne!(lhs, Right::new("different"));
    assert!(!lhs.type_eq(&Right::new(1u8)));
    assert_ne!(lhs, Right::new(1u8));
    assert_eq!(Left::new(1u8), Right::new(1u8));

    let missing = Left::new(LeftOnly);
    let other = Right::new(RightOnly);
    assert!(!missing.type_eq(&other));
    assert_ne!(missing, other);
    assert_ne!(lhs, other);
    assert_ne!(missing, rhs);

    let disjoint: Union![RightOnly] = RightOnly.into();
    assert!(!lhs.type_eq(&disjoint));
    assert_ne!(lhs, disjoint);
    assert_ne!(disjoint, lhs);
}

#[test]
fn partial_order_across_overlapping_lists() {
    #[derive(Element)]
    struct LeftOnly;

    type Left = Union![LeftOnly, u8, bool];
    type Right = Union![bool, char, u8];

    for (left, right, expected) in [
        (Left::new(2u8), Right::new(10u8), Some(Less)),
        (Left::new(2u8), Right::new(2u8), Some(Equal)),
        (Left::new(true), Right::new(false), Some(Greater)),
        (Left::new(2u8), Right::new(true), None),
        (Left::new(LeftOnly), Right::new(false), None),
        (Left::new(false), Right::new('a'), None),
    ] {
        assert_eq!(left.partial_cmp(&right), expected);
        assert_eq!(
            right.partial_cmp(&left),
            expected.map(|order| order.reverse())
        );
        assert_eq!(left == right, expected == Some(Equal));
        assert_eq!(left < right, expected == Some(Less));
        assert_eq!(left <= right, matches!(expected, Some(Less | Equal)));
        assert_eq!(left > right, expected == Some(Greater));
        assert_eq!(left >= right, matches!(expected, Some(Greater | Equal)));
    }

    let disjoint: Union![LeftOnly] = LeftOnly.into();
    assert_eq!(disjoint.partial_cmp(&Right::new(true)), None);
    assert_eq!(Right::new(true).partial_cmp(&disjoint), None);

    // Even within one list of totally ordered types, different active members
    // are incomparable.
    type Same = Union![u8, bool];
    assert_eq!(Same::new(0u8).partial_cmp(&Same::new(false)), None);
}

#[test]
fn type_equality_is_independent_of_payload_equality() {
    #[derive(Element)]
    struct Opaque;

    let opaque: Union![u8, Opaque] = Union::new(Opaque);
    let same: Union![Opaque, u8] = Union::new(Opaque);
    assert!(opaque.type_eq(&same));

    let nan: Union![f32, bool] = Union::new(f32::NAN);
    let reordered: Union![bool, f32] = Union::new(f32::NAN);
    assert!(nan.type_eq(&reordered));
    assert_ne!(nan, reordered);
    assert_ne!(nan, nan);
    assert_eq!(nan.partial_cmp(&reordered), None);
    assert_eq!(reordered.partial_cmp(&nan), None);
    assert_eq!(nan.partial_cmp(&nan), None);
}

#[derive(Clone, Debug, Element)]
struct CountDrops(Rc<Cell<usize>>);

impl Drop for CountDrops {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

#[derive(Debug, Element)]
#[repr(align(64))]
struct Aligned;

#[test]
fn ownership_survives_reordering_and_alignment_changes() {
    let drops = Rc::new(Cell::new(0));
    let value: Union![u8, CountDrops] = Union::new(CountDrops(drops.clone()));
    let copy = value.clone();
    let wide: Union![Aligned, CountDrops, bool, u8] = value.broaden();
    let subset = wide.narrow::<T![u8, CountDrops]>().unwrap();
    let remaining = subset.try_unwrap::<u8>().unwrap_err();
    let tracked = remaining.into_inner();
    assert_eq!(drops.get(), 0);
    drop(copy);
    assert_eq!(drops.get(), 1);
    drop(tracked);
    assert_eq!(drops.get(), 2);

    let value: Union![Aligned, bool, u8] = Union::new(Aligned);
    let rest = value.narrow::<T![u8, bool]>().unwrap_err();
    assert!(core::ptr::from_ref(rest.get::<Aligned>().unwrap()).is_aligned());
}

#[test]
fn derived_elements_with_the_same_name_in_different_modules() {
    macro_rules! members {
        ($($module:ident),*) => { $(mod $module {
            #[derive(tsum::union::Element)]
            pub struct Member;
        })* };
    }
    members!(first, second);
    let value: Union![first::Member, second::Member, bool] = Union::new(second::Member);
    assert!(value.get::<first::Member>().is_none());
    assert!(value.get::<second::Member>().is_some());
}

#[test]
fn match_union() {
    #[derive(Element)]
    struct Port(u16);

    let value: Union![Port, bool] = Union::new(Port(443));
    let name = match_union!(match value {
        Port(port) if port == 443 => "https",
        Port(_) => "other port",
        _ => "flag",
    });
    assert_eq!(name, "https");
}
