use core::{
    any::TypeId,
    cell::Cell,
    cmp::Ordering,
    hash::{Hash, Hasher},
};
use std::{collections::hash_map::DefaultHasher, rc::Rc};

use tsum::{T, Union, union::Element};

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
    assert_eq!(copy.cmp(&value), Ordering::Less);
    assert!(Value::new(true) < copy);
    assert_ne!(Value::new(false), Value::new(0i32));
    assert_eq!(hash(&value), hash((1u8, 9i32)));
    assert_eq!(hash(Value::new(true)), hash((0u8, true)));

    let nan = <Union![bool, f32]>::new(f32::NAN);
    assert_ne!(nan, nan);
    assert_eq!(nan.partial_cmp(&nan), None);
    assert!(nan > Union::new(true));
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
