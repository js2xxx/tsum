use core::{
    any::{TypeId, type_name},
    error::Error,
    fmt,
    hash::Hasher,
    iter::FusedIterator,
    mem::ManuallyDrop,
    pin::Pin,
};

use super::repr::{Cons, Nil, SumList};

pub(super) trait SumClone: SumList {
    unsafe fn clone(this: &Self::Repr, tag: usize) -> ManuallyDrop<Self::Repr>;
}

impl SumClone for () {
    unsafe fn clone(nil: &Self::Repr, _: usize) -> ManuallyDrop<Nil>
    where
        Self: Clone,
    {
        match nil.0 {}
    }
}

impl<Head, Tail> SumClone for (Head, Tail)
where
    Head: Clone,
    Tail: SumClone,
{
    unsafe fn clone(this: &Self::Repr, tag: usize) -> ManuallyDrop<Self::Repr> {
        ManuallyDrop::new(if tag == 0 {
            let data = unsafe { this.data.clone() };
            Cons { data }
        } else {
            let next = unsafe { Tail::clone(&this.next, tag - 1) };
            Cons { next }
        })
    }
}

pub(super) trait SumDebug: SumList {
    unsafe fn debug(this: &Self::Repr, tag: usize) -> &dyn fmt::Debug;
}

impl SumDebug for () {
    unsafe fn debug(this: &Self::Repr, _: usize) -> &dyn fmt::Debug {
        &this.0
    }
}

impl<Head, Tail> SumDebug for (Head, Tail)
where
    Head: fmt::Debug,
    Tail: SumDebug,
{
    unsafe fn debug(this: &Self::Repr, tag: usize) -> &dyn fmt::Debug {
        if tag == 0 {
            unsafe { &*this.data }
        } else {
            unsafe { Tail::debug(&this.next, tag - 1) }
        }
    }
}

pub(super) trait SumDisplay: SumList {
    unsafe fn display(this: &Self::Repr, tag: usize) -> &dyn fmt::Display;
}

impl SumDisplay for () {
    unsafe fn display(this: &Self::Repr, _: usize) -> &dyn fmt::Display {
        &this.0
    }
}

impl<Head, Tail> SumDisplay for (Head, Tail)
where
    Head: fmt::Display,
    Tail: SumDisplay,
{
    unsafe fn display(this: &Self::Repr, tag: usize) -> &dyn fmt::Display {
        if tag == 0 {
            unsafe { &*this.data }
        } else {
            unsafe { Tail::display(&this.next, tag - 1) }
        }
    }
}

pub trait TypeMeta: SumList {
    fn type_id(tag: usize) -> TypeId
    where
        Self: 'static;

    fn type_name(tag: usize) -> &'static str;

    unsafe fn as_any(this: &Self::Repr, tag: usize) -> &dyn core::any::Any
    where
        Self: 'static;

    unsafe fn as_mut_any(this: &mut Self::Repr, tag: usize) -> &mut dyn core::any::Any
    where
        Self: 'static;
}

impl TypeMeta for () {
    fn type_id(_: usize) -> TypeId {
        unreachable!()
    }

    fn type_name(_: usize) -> &'static str {
        "<uninhabited>"
    }

    unsafe fn as_any(_: &Self::Repr, _: usize) -> &dyn core::any::Any {
        unreachable!()
    }

    unsafe fn as_mut_any(_: &mut Self::Repr, _: usize) -> &mut dyn core::any::Any {
        unreachable!()
    }
}

impl<Head, Tail> TypeMeta for (Head, Tail)
where
    Tail: TypeMeta,
{
    fn type_id(tag: usize) -> TypeId
    where
        Head: 'static,
        Tail: 'static,
    {
        if tag == 0 {
            TypeId::of::<Head>()
        } else {
            Tail::type_id(tag - 1)
        }
    }

    fn type_name(tag: usize) -> &'static str {
        if tag == 0 {
            type_name::<Head>()
        } else {
            Tail::type_name(tag - 1)
        }
    }

    unsafe fn as_any(this: &Self::Repr, tag: usize) -> &dyn core::any::Any
    where
        Head: 'static,
        Tail: 'static,
    {
        if tag == 0 {
            unsafe { &*this.data }
        } else {
            unsafe { Tail::as_any(&this.next, tag - 1) }
        }
    }

    unsafe fn as_mut_any(this: &mut Self::Repr, tag: usize) -> &mut dyn core::any::Any
    where
        Self: 'static,
    {
        if tag == 0 {
            unsafe { &mut *this.data }
        } else {
            unsafe { Tail::as_mut_any(&mut this.next, tag - 1) }
        }
    }
}

pub(super) trait SumPartialEq: SumList {
    unsafe fn eq(this: &Self::Repr, other: &Self::Repr, tag: usize) -> bool;
}

impl SumPartialEq for () {
    unsafe fn eq(_: &Self::Repr, _: &Self::Repr, _: usize) -> bool {
        true
    }
}

impl<Head, Tail> SumPartialEq for (Head, Tail)
where
    Head: PartialEq,
    Tail: SumPartialEq,
{
    unsafe fn eq(this: &Self::Repr, other: &Self::Repr, tag: usize) -> bool {
        if tag == 0 {
            unsafe { this.data == other.data }
        } else {
            unsafe { Tail::eq(&this.next, &other.next, tag - 1) }
        }
    }
}

pub(super) trait SumPartialOrd: SumList + SumPartialEq {
    unsafe fn partial_cmp(
        this: &Self::Repr,
        other: &Self::Repr,
        tag: usize,
    ) -> Option<core::cmp::Ordering>;
}

impl SumPartialOrd for () {
    unsafe fn partial_cmp(_: &Self::Repr, _: &Self::Repr, _: usize) -> Option<core::cmp::Ordering> {
        Some(core::cmp::Ordering::Equal)
    }
}

impl<Head, Tail> SumPartialOrd for (Head, Tail)
where
    Head: PartialOrd,
    Tail: SumPartialOrd,
{
    unsafe fn partial_cmp(
        this: &Self::Repr,
        other: &Self::Repr,
        tag: usize,
    ) -> Option<core::cmp::Ordering> {
        if tag == 0 {
            unsafe { this.data.partial_cmp(&other.data) }
        } else {
            unsafe { Tail::partial_cmp(&this.next, &other.next, tag - 1) }
        }
    }
}

pub(super) trait SumOrd: SumList + SumPartialOrd {
    unsafe fn cmp(this: &Self::Repr, other: &Self::Repr, tag: usize) -> core::cmp::Ordering;
}

impl SumOrd for () {
    unsafe fn cmp(_: &Self::Repr, _: &Self::Repr, _: usize) -> core::cmp::Ordering {
        core::cmp::Ordering::Equal
    }
}

impl<Head, Tail> SumOrd for (Head, Tail)
where
    Head: Ord,
    Tail: SumOrd,
{
    unsafe fn cmp(this: &Self::Repr, other: &Self::Repr, tag: usize) -> core::cmp::Ordering {
        if tag == 0 {
            unsafe { this.data.cmp(&other.data) }
        } else {
            unsafe { Tail::cmp(&this.next, &other.next, tag - 1) }
        }
    }
}

pub trait SumHash: SumList {
    unsafe fn hash<H: Hasher>(this: &Self::Repr, tag: usize, state: &mut H);
}

impl SumHash for () {
    unsafe fn hash<H: Hasher>(_: &Self::Repr, _: usize, _: &mut H) {}
}

impl<Head, Tail> SumHash for (Head, Tail)
where
    Head: core::hash::Hash,
    Tail: SumHash,
{
    unsafe fn hash<H: Hasher>(this: &Self::Repr, tag: usize, state: &mut H) {
        if tag == 0 {
            unsafe { this.data.hash(state) }
        } else {
            unsafe { Tail::hash(&this.next, tag - 1, state) }
        }
    }
}

pub trait SumIterator: SumList {
    type Item;

    unsafe fn next(this: &mut Self::Repr, tag: usize) -> Option<Self::Item>;

    unsafe fn size_hint(this: &Self::Repr, tag: usize) -> (usize, Option<usize>);
}

impl<Head> SumIterator for (Head, ())
where
    Head: Iterator,
{
    type Item = Head::Item;

    unsafe fn next(this: &mut Self::Repr, tag: usize) -> Option<Self::Item> {
        debug_assert_eq!(tag, 0);
        unsafe { this.data.next() }
    }

    unsafe fn size_hint(this: &Self::Repr, tag: usize) -> (usize, Option<usize>) {
        debug_assert_eq!(tag, 0);
        unsafe { this.data.size_hint() }
    }
}

impl<Head, THead, Tail> SumIterator for (Head, (THead, Tail))
where
    Head: Iterator,
    (THead, Tail): SumIterator<Item = Head::Item>,
{
    type Item = Head::Item;

    unsafe fn next(this: &mut Self::Repr, tag: usize) -> Option<Self::Item> {
        if tag == 0 {
            unsafe { this.data.next() }
        } else {
            unsafe { <(THead, Tail)>::next(&mut this.next, tag - 1) }
        }
    }

    unsafe fn size_hint(this: &Self::Repr, tag: usize) -> (usize, Option<usize>) {
        if tag == 0 {
            unsafe { this.data.size_hint() }
        } else {
            unsafe { <(THead, Tail)>::size_hint(&this.next, tag - 1) }
        }
    }
}

pub trait SumExactSizeIterator: SumList + SumIterator {
    unsafe fn len(this: &Self::Repr, tag: usize) -> usize;
}

impl<Head> SumExactSizeIterator for (Head, ())
where
    Head: ExactSizeIterator,
{
    unsafe fn len(this: &Self::Repr, tag: usize) -> usize {
        debug_assert_eq!(tag, 0);
        unsafe { this.data.len() }
    }
}

impl<Head, THead, Tail> SumExactSizeIterator for (Head, (THead, Tail))
where
    Head: ExactSizeIterator,
    (THead, Tail): SumExactSizeIterator<Item = Head::Item>,
{
    unsafe fn len(this: &Self::Repr, tag: usize) -> usize {
        if tag == 0 {
            unsafe { this.data.len() }
        } else {
            unsafe { <(THead, Tail)>::len(&this.next, tag - 1) }
        }
    }
}

pub trait SumFusedIterator: SumList + SumIterator {}

impl<Head> SumFusedIterator for (Head, ()) where Head: FusedIterator {}

impl<Head, THead, Tail> SumFusedIterator for (Head, (THead, Tail))
where
    Head: FusedIterator,
    (THead, Tail): SumFusedIterator<Item = Head::Item>,
{
}

pub trait SumDoubleEndedIterator: SumList + SumIterator {
    unsafe fn next_back(this: &mut Self::Repr, tag: usize) -> Option<Self::Item>;
}

impl<Head> SumDoubleEndedIterator for (Head, ())
where
    Head: DoubleEndedIterator,
{
    unsafe fn next_back(this: &mut Self::Repr, tag: usize) -> Option<Self::Item> {
        debug_assert_eq!(tag, 0);
        unsafe { this.data.next_back() }
    }
}

impl<Head, THead, Tail> SumDoubleEndedIterator for (Head, (THead, Tail))
where
    Head: DoubleEndedIterator,
    (THead, Tail): SumDoubleEndedIterator<Item = Head::Item>,
{
    unsafe fn next_back(this: &mut Self::Repr, tag: usize) -> Option<Self::Item> {
        if tag == 0 {
            unsafe { this.data.next_back() }
        } else {
            unsafe { <(THead, Tail)>::next_back(&mut this.next, tag - 1) }
        }
    }
}

pub trait SumFuture: SumList {
    type Output;

    unsafe fn poll(
        this: Pin<&mut Self::Repr>,
        tag: usize,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output>;
}

impl<Head> SumFuture for (Head, ())
where
    Head: Future,
{
    type Output = Head::Output;

    unsafe fn poll(
        this: Pin<&mut Self::Repr>,
        tag: usize,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        debug_assert_eq!(tag, 0);
        // SAFETY: The `Pin` guarantees that the data is not moved.
        unsafe { this.map_unchecked_mut(|t| &mut *t.data).poll(cx) }
    }
}

impl<Head, THead, Tail> SumFuture for (Head, (THead, Tail))
where
    Head: Future,
    (THead, Tail): SumFuture<Output = Head::Output>,
{
    type Output = Head::Output;

    unsafe fn poll(
        this: Pin<&mut Self::Repr>,
        tag: usize,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        if tag == 0 {
            // SAFETY: The `Pin` guarantees that the data is not moved.
            unsafe { this.map_unchecked_mut(|t| &mut *t.data).poll(cx) }
        } else {
            // SAFETY: The `Pin` guarantees that the data is not moved.
            unsafe { <(THead, Tail)>::poll(this.map_unchecked_mut(|t| &mut *t.next), tag - 1, cx) }
        }
    }
}

pub(super) trait SumError: SumDebug + SumDisplay {
    unsafe fn source(this: &Self::Repr, tag: usize) -> Option<&(dyn Error + 'static)>;
}

impl SumError for () {
    unsafe fn source(this: &Self::Repr, _: usize) -> Option<&(dyn Error + 'static)> {
        this.0
    }
}

impl<Head, Tail> SumError for (Head, Tail)
where
    Head: Error,
    Tail: SumError,
{
    unsafe fn source(this: &Self::Repr, tag: usize) -> Option<&(dyn Error + 'static)> {
        if tag == 0 {
            unsafe { this.data.source() }
        } else {
            unsafe { Tail::source(&this.next, tag - 1) }
        }
    }
}
