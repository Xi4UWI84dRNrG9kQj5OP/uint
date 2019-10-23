use std::mem;
use std::ops::{Shl, Shr, Add, AddAssign, Sub, SubAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Rem};
use std::convert::TryFrom;
use std::fmt::{Display, Debug};
use std::num::TryFromIntError;
use std::cmp::Ordering;

#[allow(non_camel_case_types, dead_code)]
pub type u40 = UIntPair<u8>;

#[allow(non_camel_case_types, dead_code)]
pub type u48 = UIntPair<u16>;


#[derive(Copy, Clone, PartialEq, Eq)]
pub struct UIntPair<T> {
    /// member containing lower significant integer value
    low: [u8; 4],

    /// member containing higher significant integer value
    high: T,
}

impl<T: Int> UIntPair<T> {
    /// number of bits in the lower integer part, used a bit shift value.
    const LOW_BITS: usize = 8 * mem::size_of::<u32>();

    /// number of bits in the higher integer part, used a bit shift value.
    const HIGH_BITS: usize = 8 * mem::size_of::<T>();

    /// number of binary digits (bits) in UIntPair
    const DIGITS: usize = Self::LOW_BITS + Self::HIGH_BITS;

    /// construct unit pair from lower and higher parts.
    pub fn new<E: Into<Self>>(val: E) -> Self {
        val.into()
    }
}

impl<T: Int> Debug for UIntPair<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&u64::from(*self),f)
    }
}

use num::Bounded;
impl<T: Int + Bounded> std::default::Default for UIntPair<T> {
    fn default() -> Self { Self::min_value() }
}

impl<T: num::Bounded> num::Bounded for UIntPair<T> {
    fn min_value() -> Self {
        Self {
            low: [0; 4],
            high: T::min_value(),
        }
    }

    fn max_value() -> Self {
        Self {
            low: [1; 4],
            high: T::min_value(),
        }
    }
}

macro_rules! impl_UIntPair_traits {
    ($($int:ty)*) => {
        $(
            /// partial eq (==) with right site $int
            impl<T: Int> PartialEq<$int> for UIntPair<T> {
                fn eq(&self, other: &$int) -> bool {
                    self.eq(&Self::from(*other))
                }
            }

            /// partial eq (==) with left site $int 
            impl<T: Int> PartialEq<UIntPair<T>> for $int {
                fn eq(&self, other: &UIntPair<T>) -> bool {
                    other.eq(self)
                }
            }

            /// PartialOrd implementation (<=) for $int on the right site
            impl<T: Int> PartialOrd<$int> for UIntPair<T> {
                fn partial_cmp(&self, other: &$int) -> Option<Ordering> {
                    u64::from(*self).partial_cmp(&u64::from(*other))
                }
            }

            /// PartialOrd implementation (<=) for $int on the left site
            impl<T: Int> PartialOrd<UIntPair<T>> for $int {
                fn partial_cmp(&self, other: &UIntPair<T>) -> Option<Ordering> {
                    u64::from(*self).partial_cmp(&u64::from(*other))
                }
            }

            /// BitAnd (&) for right site $int
            impl<T: Int> BitAnd<$int> for UIntPair<T> {
                type Output = Self;

                // rhs is the "right-hand side" of the expression `a & b`
                fn bitand(self, rhs: $int) -> Self::Output {
                    let low_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(self.low) }.to_le();
                    let new_low = low_as_arr & rhs as u32;
                
                    Self {
                        low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
                        high: self.high 
                    }
                }
            }

            /// BitAnd (&) for left site $int
            impl<T: Int> BitAnd<UIntPair<T>> for $int {
                type Output = UIntPair<T>;

                // rhs is the "right-hand side" of the expression `a & b`
                fn bitand(self, rhs: UIntPair<T>) -> Self::Output {
                    let low_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(rhs.low) }.to_le();
                    let new_low = low_as_arr & self as u32;

                    UIntPair {
                        low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
                        high: rhs.high 
                    }
                }
            }

            /// BitOr (|) for right site $int
            impl<T: Int> BitOr<$int> for UIntPair<T> {
                type Output = Self;

                fn bitor(self, rhs: $int) -> Self::Output {
                    let low_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(self.low) }.to_le();
                    let new_low = low_as_arr | rhs as u32;
                
                    Self {
                        low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
                        high: self.high 
                    }
                }
            }

            /// BitOr (|) for left site $int
            impl<T: Int> BitOr<UIntPair<T>> for $int {
                type Output = UIntPair<T>;

                fn bitor(self, rhs: UIntPair<T>) -> Self::Output {
                    let low_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(rhs.low) }.to_le();
                    let new_low = low_as_arr | self as u32;

                    UIntPair {
                        low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
                        high: rhs.high 
                    }
                }
            }

            /// BitXor (^) for right site $int
            impl<T: Int> BitXor<$int> for UIntPair<T> {
                type Output = Self;

                fn bitxor(self, rhs: $int) -> Self::Output {
                    let low_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(self.low) }.to_le();
                    let new_low = low_as_arr ^ rhs as u32;
                
                    Self {
                        low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
                        high: self.high 
                    }
                }
            }

            /// BitXor (^) for left site $int
            impl<T: Int> BitXor<UIntPair<T>> for $int {
                type Output = UIntPair<T>;

                fn bitxor(self, rhs: UIntPair<T>) -> Self::Output {
                    let low_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(rhs.low) }.to_le();
                    let new_low = low_as_arr ^ self as u32;

                    UIntPair {
                        low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
                        high: rhs.high 
                    }
                }
            }

            /// subtraction-assign operator right site $int
            impl<T: Int> SubAssign<$int> for UIntPair<T> {
                fn sub_assign(&mut self, other: $int) {
                    *self = *self - other;
                }
            }
            
            /// subtraction operator right site $int
            impl<T: Int> Sub<$int> for UIntPair<T> {
                type Output = Self;

                fn sub(self, other: $int) -> Self {
                    self - Self::from(other)
                }
            }

            /// addition operator left site $int
            impl<T: Int> Sub<UIntPair<T>> for $int {
                type Output = UIntPair<T>;

                fn sub(self, other: UIntPair<T>) -> UIntPair<T> {
                    UIntPair::<T>::from(self) - other
                }
            }

            /// addition operator right site $int
            impl<T: Int> Add<$int> for UIntPair<T> {
                type Output = Self;

                fn add(self, other: $int) -> Self {
                    self + Self::from(other)
                }
            }

            /// addition operator left site $int
            impl<T: Int> Add<UIntPair<T>> for $int {
                type Output = UIntPair<T>;

                fn add(self, other: UIntPair<T>) -> UIntPair<T> {
                    other + self
                }
            }

            /// Bitshift left for right site $int
            impl<T: Int> Shl<$int> for UIntPair<T> {
                type Output = Self;

                fn shl(self, rhs: $int) -> Self {
                    (u64::from(self) << u64::from(rhs)).into()
                }
            }

            /// Bitshift left for right site UIntPair<T> left site $int
            impl<T: Int> Shl<UIntPair<T>> for $int {
                type Output = UIntPair<T>;

                fn shl(self, rhs: UIntPair<T>) -> UIntPair<T> {
                    (UIntPair::<T>::from(self) << rhs)
                }
            }

            
            /// Bitshift right for right site $int
            impl<T: Int> Shr<$int> for UIntPair<T> {
                type Output = Self;

                fn shr(self, rhs: $int) -> Self {
                    (u64::from(self) >> u64::from(rhs)).into()
                }
            }

            /// Bitshift right for right site UIntPair<T> left site $int
            impl<T: Int> Shr<UIntPair<T>> for $int {
                type Output = UIntPair<T>;

                fn shr(self, rhs: UIntPair<T>) -> UIntPair<T> {
                    (UIntPair::<T>::from(self) >> rhs)
                }
            }
        )*
    }
}

impl_UIntPair_traits!(u8 u16 u32);

/// Bitshift left for right site UIntPair<T>
impl<T: Int> Shl for UIntPair<T> {
    type Output = Self;

    fn shl(self, rhs: Self) -> Self {
        (u64::from(self) << u64::from(rhs)).into()
    }
}

/// Bitshift left for right site u64
impl<T: Int> Shl<u64> for UIntPair<T> {
    type Output = u64;

    fn shl(self, rhs: u64) -> u64 {
        (u64::from(self) << rhs)
    }
}

/// Bitshift left for right site i32
impl<T: Int> Shl<i32> for UIntPair<T> {
    type Output = Self;

    fn shl(self, rhs: i32) -> Self {
        if rhs < 0 {
            panic!("To small value for Bitshift.")
        }

        (u64::from(self) << rhs as u64).into()
    }
}

/// Bitshift left for right site i32
impl<T: Int> Shr<i32> for UIntPair<T> {
    type Output = Self;

    fn shr(self, rhs: i32) -> Self {
        if rhs < 0 {
            panic!("To small value for Bitshift.")
        }

        (u64::from(self) >> rhs as u64).into()
    }
}

/// Bitshift left for right site UIntPair<T> left site u64
impl<T: Int> Shl<UIntPair<T>> for u64 {
    type Output = u64;

    fn shl(self, rhs: UIntPair<T>) -> u64 {
        (self << u64::from(rhs))
    }
}

/// Bitshift right for right site UIntPair<T>
impl<T: Int> Shr for UIntPair<T> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self {
        (u64::from(self) >> u64::from(rhs)).into()
    }
}

/// Bitshift right for right site u64
impl<T: Int> Shr<u64> for UIntPair<T> {
    type Output = u64;

    fn shr(self, rhs: u64) -> u64 {
        (u64::from(self) >> rhs)
    }
}

/// Bitshift right for right site UIntPair<T> left site u64
impl<T: Int> Shr<UIntPair<T>> for u64 {
    type Output = u64;

    fn shr(self, rhs: UIntPair<T>) -> u64 {
        (self >> u64::from(rhs))
    }
}

/// partial eq (==) with right site u64
impl<T: Int> PartialEq<u64> for UIntPair<T> {
    fn eq(&self, other: &u64) -> bool {
        self.eq(&Self::from(*other))
    }
}

/// partial eq (==) with left site u64
impl<T: Int> PartialEq<UIntPair<T>> for u64 {
    fn eq(&self, other: &UIntPair<T>) -> bool {
        other.eq(self)
    }
}

/// partial eq (==) with right site i32
impl<T: Int> PartialEq<i32> for UIntPair<T> {
    fn eq(&self, other: &i32) -> bool {
        self.eq(&Self::from(*other))
    }
}

/// partial eq (==) with left site i32
impl<T: Int> PartialEq<UIntPair<T>> for i32 {
    fn eq(&self, other: &UIntPair<T>) -> bool {
        other.eq(self)
    }
}

/// PartialOrd implementation (<=) for UIntPair<T> on the right site
impl<T: Int> PartialOrd for UIntPair<T> {
    fn partial_cmp(&self, other: &UIntPair<T>) -> Option<Ordering> {
        u64::from(*self).partial_cmp(&u64::from(*other))
    }
}

/// PartialOrd implementation (<=) for u64 on the right site
impl<T: Int> PartialOrd<u64> for UIntPair<T> {
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        u64::from(*self).partial_cmp(other)
    }
}

/// PartialOrd implementation (<=) for u64 on the left site
impl<T: Int> PartialOrd<UIntPair<T>> for u64 {
    fn partial_cmp(&self, other: &UIntPair<T>) -> Option<Ordering> {
        self.partial_cmp(&u64::from(*other))
    }
}

/// BitAnd (&) for right site UIntPair<T>
impl<T: Int> BitAnd for UIntPair<T> {
    type Output = Self;

    // rhs is the "right-hand side" of the expression `a & b`
    fn bitand(self, rhs: Self) -> Self::Output {
        let low_self_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(self.low) }.to_le();
        let low_rhs_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(rhs.low) }.to_le();

        let new_low = low_self_as_arr & low_rhs_as_arr;
        Self {
            low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
            high: self.high & rhs.high,
        }
    }
}

/// BitAnd (&) for right site u64
impl<T: Int> BitAnd<u64> for UIntPair<T> {
    type Output = u64;

    // rhs is the "right-hand side" of the expression `a & b`
    fn bitand(self, rhs: u64) -> Self::Output {
        u64::from(self) & rhs
    }
}

/// BitAnd (&) for left site u64
impl<T: Int> BitAnd<UIntPair<T>> for u64 {
    type Output = Self;

    // rhs is the "right-hand side" of the expression `a & b`
    fn bitand(self, rhs: UIntPair<T>) -> Self::Output {
        u64::from(rhs) & self
    }
}

/// BitOr (|) for right site UIntPair<T>
impl<T: Int> BitOr for UIntPair<T> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let low_self_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(self.low) }.to_le();
        let low_rhs_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(rhs.low) }.to_le();

        let new_low = low_self_as_arr | low_rhs_as_arr;
        Self {
            low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
            high: self.high | rhs.high,
        }
    }
}

/// BitOr (|) for right site u64
impl<T: Int> BitOr<u64> for UIntPair<T> {
    type Output = u64;

    fn bitor(self, rhs: u64) -> Self::Output {
        u64::from(self) | rhs
    }
}

/// BitOr (|) for left site u64
impl<T: Int> BitOr<UIntPair<T>> for u64 {
    type Output = Self;

    fn bitor(self, rhs: UIntPair<T>) -> Self::Output {
        u64::from(rhs) | self
    }
}

/// BitXor (^) for right site UIntPair<T>
impl<T: Int> BitXor for UIntPair<T> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let low_self_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(self.low) }.to_le();
        let low_rhs_as_arr = unsafe { std::mem::transmute::<[u8; 4], u32>(rhs.low) }.to_le();

        let new_low = low_self_as_arr ^ low_rhs_as_arr;
        Self {
            low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
            high: self.high ^ rhs.high,
        }
    }
}

/// BitXor (^) for right site u64
impl<T: Int> BitXor<u64> for UIntPair<T> {
    type Output = u64;

    fn bitxor(self, rhs: u64) -> Self::Output {
        u64::from(self) ^ rhs
    }
}

/// BitXor (^)for left site u64
impl<T: Int> BitXor<UIntPair<T>> for u64 {
    type Output = Self;

    fn bitxor(self, rhs: UIntPair<T>) -> Self::Output {
        u64::from(rhs) ^ self
    }
}

/// Ermöglicht die Konvertierung von u32 nach UIntPair.
impl<T: Int> From<u32> for UIntPair<T> {
    fn from(item: u32) -> Self {
        Self {
            low: unsafe { std::mem::transmute::<u32, [u8; 4]>(item) },
            high: T::MIN_VALUE,
        }
    }
}

/// Ermöglicht die Konvertierung von i32 nach UIntPair.
impl<T: Int> From<i32> for UIntPair<T> {
    fn from(item: i32) -> Self {
        if item >= 0 {
            Self::from(item as u32)
        } else {
            Self {
                low: unsafe { std::mem::transmute::<i32, [u8; 4]>(item) },
                high: T::MAX_VALUE,
            }
        }
    }
}

/// Ermöglicht die Konvertierung von u16 nach UIntPair.
impl<T: Int> From<u16> for UIntPair<T> {
    fn from(item: u16) -> Self {
        Self::from(item as u32)
    }
}

/// Ermöglicht die Konvertierung von i16 nach UIntPair.
impl<T: Int> From<i16> for UIntPair<T> {
    fn from(item: i16) -> Self {
        Self::from(item as i32)
    }
}

/// Ermöglicht die Konvertierung von u8 nach UIntPair.
impl<T: Int> From<u8> for UIntPair<T> {
    fn from(item: u8) -> Self {
        Self::from(item as u32)
    }
}

/// Ermöglicht die Konvertierung von i8 nach UIntPair.
impl<T: Int> From<i8> for UIntPair<T> {
    fn from(item: i8) -> Self {
        Self::from(item as i32)
    }
}

/// Ermöglicht die Konvertierung von UIntPair nach u64.
impl<T: Int> From<UIntPair<T>> for u64 {
    fn from(item: UIntPair<T>) -> Self {
        let low_bits: u64 = (UIntPair::<T>::LOW_BITS as u8).into();
        item.high.into() << low_bits | (unsafe { std::mem::transmute::<[u8; 4], u32>(item.low) }.to_le() as u64)
    }
}

/// Ermöglicht die Konvertierung von UIntPair nach i64.
impl<T: Int> From<UIntPair<T>> for i64 {
    fn from(item: UIntPair<T>) -> Self {
        u64::from(item) as i64
    }
}

/// bitAnd-assign operator right site with all possible types (except u64)
impl<T: Int, R: BitAnd<Self, Output=Self>> BitAndAssign<R> for UIntPair<T> {
    fn bitand_assign(&mut self, other: R) {
        *self = other & *self;
    }
}

/// bitAnd-assign operator right site with u64
impl<T: Int> BitAndAssign<u64> for UIntPair<T> {
    fn bitand_assign(&mut self, other: u64) {
        *self = Self::from(other & *self);
    }
}

/// bitOr-assign operator right site with all possible types (except u64)
impl<T: Int, R: BitOr<Self, Output=Self>> BitOrAssign<R> for UIntPair<T> {
    fn bitor_assign(&mut self, other: R) {
        *self = other | *self;
    }
}

/// bitOr-assign operator right site with u64
impl<T: Int> BitOrAssign<u64> for UIntPair<T> {
    fn bitor_assign(&mut self, other: u64) {
        *self = Self::from(other | *self);
    }
}

/// bitXor-assign operator right site with all possible types (except u64)
impl<T: Int, R: BitXor<Self, Output=Self>> BitXorAssign<R> for UIntPair<T> {
    fn bitxor_assign(&mut self, other: R) {
        *self = other ^ *self;
    }
}

/// bitXor-assign operator right site with u64
impl<T: Int> BitXorAssign<u64> for UIntPair<T> {
    fn bitxor_assign(&mut self, other: u64) {
        *self = Self::from(other ^ *self);
    }
}

/// addition-assign operator right site with all possible types (except u64)
impl<T: Int, R: Add<Self, Output=Self>> AddAssign<R> for UIntPair<T> {
    fn add_assign(&mut self, other: R) {
        *self = other + *self;
    }
}

/// addition-assign operator right site with all possible types (except u64)
impl<T: Int> AddAssign<u64> for UIntPair<T> {
    fn add_assign(&mut self, other: u64) {
        *self = Self::from(*self + other);
    }
}


/// subtraction-assign operator right site u64
impl<T: Int> SubAssign<u64> for UIntPair<T> {
    fn sub_assign(&mut self, other: u64) {
        *self = *self - other as u32;
    }
}

/// subtraction operator right site UIntPair<T>
impl<T: Int> Sub for UIntPair<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        (u64::from(self) - u64::from(other)).into()
    }
}

/// subtraction operator right site u64
impl<T: Int> Sub<u64> for UIntPair<T> {
    type Output = u64;

    fn sub(self, other: u64) -> u64 {
        (self - Self::from(other)).into()
    }
}

/// addition operator left site u64
impl<T: Int> Sub<UIntPair<T>> for u64 {
    type Output = Self;

    fn sub(self, other: UIntPair<T>) -> Self {
        (UIntPair::<T>::from(self) - other).into()
    }
}


/// addition operator right site UIntPair<T>
impl<T: Int> Add for UIntPair<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let add_low = (unsafe { std::mem::transmute::<[u8; 4], u32>(self.low) }.to_le() as u64).wrapping_add(unsafe { std::mem::transmute::<[u8; 4], u32>(other.low) }.to_le() as u64);
        let add_high = (add_low >> Self::LOW_BITS) as u8;

        let new_low = (add_low & u32::max_value() as u64) as u32;
        Self {
            low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low) },
            high: self.high + other.high + (T::from(add_high) & T::MAX_VALUE),
        }
    }
}

/// addition operator right site u64
impl<T: Int> Add<u64> for UIntPair<T> {
    type Output = Self;

    fn add(self, other: u64) -> Self {
        self + Self::from(other)
    }
}

/// addition operator left site u64
impl<T: Int> Add<UIntPair<T>> for u64 {
    type Output = Self;

    fn add(self, other: UIntPair<T>) -> Self {
        u64::from(other + self)
    }
}


/// remainder operator right site UIntPair<T>
impl<T: Int> Rem for UIntPair<T> {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        Self {
            low: unsafe{std::mem::transmute::<u32, [u8; 4]>(std::mem::transmute::<[u8; 4], u32>(self.low) % std::mem::transmute::<[u8; 4], u32>(other.low))},
            high: T::from(0),
        }
    }
}

/// remainder operator right site u64
impl<T: Int> Rem<u64> for UIntPair<T> {
    type Output = Self;

    fn rem(self, other: u64) -> Self {
        self % Self::from(other)
    }
}

/// remainder operator left site u64
impl<T: Int> Rem<UIntPair<T>> for u64 {
    type Output = Self;

    fn rem(self, other: UIntPair<T>) -> Self {
        u64::from(other % self)
    }
}

/// Ermöglicht die Konvertierung von u64 nach UIntPair.
impl<T: Int> From<u64> for UIntPair<T> {
    fn from(item: u64) -> Self {
        assert!(item >> Self::DIGITS == 0, "You tried to convert a real u64 into a smaller value. You would lose information.");

        let new_low = item & u32::max_value() as u64;
        let high = (item >> Self::LOW_BITS) & T::MAX_VALUE.into();

        Self {
            low: unsafe { std::mem::transmute::<u32, [u8; 4]>(new_low as u32) },
            high: T::try_from(high).expect("From<u64> for UIntPair<T> ist schiefgelaufen."),
        }
    }
}

/// Ermöglicht die Konvertierung von i64 nach UIntPair.
impl<T: Int> From<i64> for UIntPair<T> {
    fn from(item: i64) -> Self {
        assert!(item < 0, "You tried to convert a negativ i64 into a u40. This operation isn't supported.");
        Self::from(item as u64)
    }
}

/// Ermöglicht das Sortieren der Werte
impl<T: Int> Ord for UIntPair<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        u64::from(*self).cmp(&u64::from(*other))
    }
}

impl<T: Int> Display for UIntPair<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&u64::from(*self),f)
    }
}

/// Stellt sicher, dass der Wert (in high) einen Maximal- und Minimalwert besitzt.
pub trait Int: Into<u64> + From<u8> + Copy + Shl<Output=Self> + Add<Output=Self> 
          + BitAnd<Output=Self> + Debug + TryFrom<u64, Error=TryFromIntError> + Sub<Output=Self> 
          + Typable + PartialEq + BitAnd<Output=Self> + BitOr<Output=Self> + BitXor<Output=Self> + Eq  {
    const MAX_VALUE: Self;
    const MIN_VALUE: Self;
    fn wrapping_add(self, rhs: Self) -> Self;
    fn wrapping_sub(self, rhs: Self) -> Self;
}

pub trait Typable: Display + num::Bounded {
    const TYPE: &'static str; 
}



impl Typable for u8 {
    const TYPE: &'static str = "u8";
}

impl Typable for u16 {
    const TYPE: &'static str = "u16";
}


impl Typable for u32 {
    const TYPE: &'static str = "u32";
}

impl Typable for u64 {
    const TYPE: &'static str = "u64";
}

impl Typable for u40 {
    const TYPE: &'static str = "u40";
}

impl Typable for u48 {
    const TYPE: &'static str = "u48";
}


impl Int for u32 {
    const MAX_VALUE: Self = Self::max_value();
    const MIN_VALUE: Self = Self::min_value();
    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_sub(self, rhs: Self) -> Self {
        self.wrapping_sub(rhs)
    }
}

impl Int for u16 {
    const MAX_VALUE: Self = Self::max_value();
    const MIN_VALUE: Self = Self::min_value();
    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_sub(self, rhs: Self) -> Self {
        self.wrapping_sub(rhs)
    }
}

impl Int for u8 {
    const MAX_VALUE: Self = Self::max_value();
    const MIN_VALUE: Self = Self::min_value();
    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_sub(self, rhs: Self) -> Self {
        self.wrapping_sub(rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::u40;
    use num::Bounded;
    /// subs and assign values
    #[test]
    fn test_sub_assign_random() {
        let mut b = u40::max_value();
        let mut c = u40::max_value();
        let mut d = u40::max_value();

        let mut right_val: u64 = u40::max_value().into();
        for i in 0..u16::max_value() {
            b -= i as u16;
            c -= i as u32;
            d -= i as u64;
            right_val = right_val.wrapping_sub(i as u64);
        }

        assert_eq!(u64::from(b), right_val);
        assert_eq!(u64::from(c), right_val);
        assert_eq!(u64::from(d), right_val);
    }

    /// sub a lot of u32 values
    #[test]
    fn test_sub_random() {
        for i in 0..(u32::max_value()) {
            for j in 0..(i + 1) {
                let x = u40::from(i);
                let y = u40::from(j);

                assert_eq!(i + j, u64::from(x + y) as u32);
            }
        }
    }

    /// adds and assign a lot of u32 values
    #[test]
    fn test_add_assign_random() {
        let mut b = u40::from(0);
        let mut c = u40::from(0);
        let mut d = u40::from(0);

        let mut right_val: u64 = 0;
        for i in 0..u16::max_value() {
            b += i as u16;
            c += i as u32;
            d += i as u64;
            right_val += i as u64;
        }

        assert_eq!(u64::from(b), right_val);
        assert_eq!(u64::from(c), right_val);
        assert_eq!(u64::from(d), right_val);
    }

    /// adds a lot of u32 values
    #[test]
    fn test_add_random() {
        for i in 0..u32::max_value() {
            for j in 0..u32::max_value() {
                let x = u40::from(i);
                let y = u40::from(j);
                assert_eq!(i + j, u64::from(x + y) as u32);
            }
        }
    }

    /// Checks the Borders off the addition
    #[test]
    fn test_add_borders() {
        let x = u40::from(0b1111111111111111111111111111111111111110 as u64);
        let y = 1 as u32;

        assert_eq!(0b1111111111111111111111111111111111111110 + 1, u64::from(y + x))
    }

    /// Checks the conversion from u8 to u40 
    #[test]
    fn test_from_u8() {
        for i in 0..u8::max_value() {
            assert_eq!(u64::from(u40::from(i)), i as u64);
        }
    }

    /// Checks the conversion from i8 to u40 
    #[test]
    fn test_from_i8() {
        for i in 0..i8::max_value() {
            assert_eq!(u64::from(u40::from(i)), i as u64);
        }
    }

    /// Checks the conversion from u16 to u40 
    #[test]
    fn test_from_u16() {
        for i in 0..u16::max_value() {
            assert_eq!(u64::from(u40::from(i)), i as u64);
        }
    }

    /// Checks the conversion from i16 to u40 
    #[test]
    fn test_from_i16() {
        for i in 0..i16::max_value() {
            assert_eq!(u64::from(u40::from(i)), i as u64);
        }
    }

    /// Checks the conversion from u32 to u40
    #[test]
    fn test_from_u32() {
        for i in 0..u32::max_value() {
            assert_eq!(u64::from(u40::from(i)), i as u64);
        }
    }

    /// Checks the conversion from i32 to u40 
    #[test]
    fn test_from_i32() {
        for i in 0..i32::max_value() {
            assert_eq!(u64::from(u40::from(i)), i as u64);
        }
    }

    /// Check all possible addition combinations
    #[test]
    fn test_all_addition() {
        let x: u8 = 25;
        let z: u16 = 30;
        let b: u32 = 40;
        let d: u64 = 80;
        let start = u40::from(0);
        assert_eq!(u64::from(start + x + z + b + d), 175);
        assert_eq!(d + (b + (z + (x + start))), 175);
    }

    /// Check all possible sub combinations
    #[test]
    fn test_all_subs() {
        let x: u8 = 25;
        let z: u16 = 30;
        let b: u32 = 40;
        let d: u64 = 80;
        let start = u40::from(1000);
        assert_eq!(u64::from(start - x - z - b - d), 825);
        assert_eq!(2000 as u64 - (start - x), 1025);
    }

    // TODO: Teste den ganzen BitAnd, BitOr, BitXor, Shr, Shl, (+Assigns), PartialEq, Add und Sub Overflows, PartialOrd Kram
}
