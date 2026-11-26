#![recursion_limit = "1024"]

use std::{
    any::TypeId,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
    mem::size_of,
};

use tsum::{
    Sum, Union,
    sum::{index::U0, repr::SumList},
};

// Prepend zero-sized members so size_of measures the discriminant alone.
type Units2<T> = ((), ((), T));
type Units4<T> = Units2<Units2<T>>;
type Units8<T> = Units4<Units4<T>>;
type Units16<T> = Units8<Units8<T>>;
type Units32<T> = Units16<Units16<T>>;
type Units64<T> = Units32<Units32<T>>;
type Units128<T> = Units64<Units64<T>>;
type Units256<T> = Units128<Units128<T>>;

#[test]
fn storage_matches_the_member_count() {
    fn unit_tag<L: SumList<Discriminant = ()>>() {}
    fn byte_tag<L: SumList<Discriminant = u8>>() {}
    fn word_tag<L: SumList<Discriminant = usize>>() {}

    unit_tag::<()>();
    unit_tag::<((), ())>();
    byte_tag::<Units2<()>>();
    byte_tag::<Units256<()>>();
    word_tag::<Units256<((), ())>>();

    assert_eq!(size_of::<Sum![]>(), 0);
    assert_eq!(size_of::<Sum![u64]>(), size_of::<u64>());
    assert_eq!(size_of::<Sum<Units2<()>>>(), 1);
    assert_eq!(size_of::<Sum<Units256<()>>>(), 1);
    assert_eq!(size_of::<Sum<Units256<((), ())>>>(), size_of::<usize>());
    assert_eq!(size_of::<Union![]>(), 0);
    assert_eq!(size_of::<Union![u64]>(), size_of::<u64>());
    assert_eq!(size_of::<Union![bool, u8]>(), 2);
}

fn hash(value: impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn last_member_survives_changes_in_tag_width() {
    type Wide = Sum<Units256<(String, ())>>;

    let value: Sum![String] = String::from("tag").into();
    assert_eq!(hash(&value), hash((0u8, "tag")));

    let mut wide: Wide = value.broaden();
    wide.get_mut::<String, _>().unwrap().push('!');
    assert_eq!(wide.type_id(), TypeId::of::<String>());
    assert!(wide > Wide::new::<(), U0>(()));

    assert_eq!(hash(&wide), hash((256usize, "tag!")));

    let copy = wide.clone().map(|s: String| s.len());
    assert_eq!(copy.try_unwrap::<usize, _>().unwrap(), 4);

    // Removing the head moves the active tag from 256 to 255. Narrowing to
    // the last member then moves it from 255 to the implicit singleton tag.
    let compact = wide.try_unwrap::<(), U0>().unwrap_err();
    assert_eq!(compact.get::<String, _>().unwrap(), "tag!");
    let singleton: Sum![String] = compact.narrow().unwrap();
    assert_eq!(singleton.into_inner(), "tag!");
}
