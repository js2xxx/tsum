#![allow(missing_docs)]

use core::marker::PhantomData;

pub struct UTerm;

pub struct UInt<U>(PhantomData<U>);

pub trait Tag {
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
