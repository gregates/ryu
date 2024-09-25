mod exponent;
mod mantissa;

use self::exponent::write_exponent2;
use self::mantissa::{write_mantissa, write_mantissa_long, write_mantissa_n_digits};
use crate::common;
use crate::d2s::{self, d2d, DOUBLE_EXPONENT_BITS, DOUBLE_MANTISSA_BITS};
use crate::f2s::{f2d, FLOAT_EXPONENT_BITS, FLOAT_MANTISSA_BITS};
use core::ptr;
#[cfg(feature = "no-panic")]
use no_panic::no_panic;

/// Print f64 to the given buffer and return number of bytes written.
///
/// ## Special cases
///
/// This function **does not** check for NaN or infinity. If the input
/// number is not a finite float, the printed representation will be some
/// correctly formatted but unspecified numerical value.
///
/// Please check [`is_finite`] yourself before calling this function, or
/// check [`is_nan`] and [`is_infinite`] and handle those cases yourself.
///
/// [`is_finite`]: https://doc.rust-lang.org/std/primitive.f64.html#method.is_finite
/// [`is_nan`]: https://doc.rust-lang.org/std/primitive.f64.html#method.is_nan
/// [`is_infinite`]: https://doc.rust-lang.org/std/primitive.f64.html#method.is_infinite
///
/// Accepts an optional precision and a byte representing an ASCII character to use
/// as decimal point.
///
/// ## Safety
///
/// The `result` pointer argument must point to sufficiently many writable bytes
/// to hold Ryū's representation of `f`.
///
/// ## Example
///
/// ```
/// use std::{mem::MaybeUninit, slice, str};
///
/// let f = 1.234f64;
///
/// unsafe {
///     let mut buffer = [MaybeUninit::<u8>::uninit(); 24];
///     let len = ryu::raw::format64(f, None, b'.', buffer.as_mut_ptr() as *mut u8);
///     let slice = slice::from_raw_parts(buffer.as_ptr() as *const u8, len);
///     let print = str::from_utf8_unchecked(slice);
///     assert_eq!(print, "1.234");
/// }
/// ```
#[must_use]
#[cfg_attr(feature = "no-panic", no_panic)]
pub unsafe fn format64(f: f64, precision: Option<usize>, decimal_point: u8, result: *mut u8) -> usize {
    match precision {
        Some(precision) => format64_fixed(f, precision, decimal_point, result),
        None => format64_inner(f, decimal_point, result),
    }
}

unsafe fn format64_inner(f: f64, decimal_point: u8, result: *mut u8) -> usize {
    let bits = f.to_bits();
    let sign = ((bits >> (DOUBLE_MANTISSA_BITS + DOUBLE_EXPONENT_BITS)) & 1) != 0;
    let ieee_mantissa = bits & ((1u64 << DOUBLE_MANTISSA_BITS) - 1);
    let ieee_exponent =
        (bits >> DOUBLE_MANTISSA_BITS) as u32 & ((1u32 << DOUBLE_EXPONENT_BITS) - 1);

    let mut index = 0isize;
    if sign {
        *result = b'-';
        index += 1;
    }

    if ieee_exponent == 0 && ieee_mantissa == 0 {
        *result.offset(index) = b'0';
        return sign as usize + 1;
    }

    let v = d2d(ieee_mantissa, ieee_exponent);

    let length = d2s::decimal_length17(v.mantissa) as isize;
    let k = v.exponent as isize;
    let kk = length + k; // 10^(kk-1) <= v < 10^kk
    debug_assert!(k >= -324);

    if 0 <= k {
        // 1234e7 -> 12340000000.0
        write_mantissa_long(v.mantissa, result.offset(index + length));
        for i in length..kk {
            *result.offset(index + i) = b'0';
        }
        index as usize + kk as usize
    } else if 0 < kk {
        // 1234e-2 -> 12.34
        write_mantissa_long(v.mantissa, result.offset(index + length + 1));
        ptr::copy(result.offset(index + 1), result.offset(index), kk as usize);
        *result.offset(index + kk) = decimal_point;
        index as usize + length as usize + 1
    } else {
        // 1234e-6 -> 0.001234
        *result.offset(index) = b'0';
        *result.offset(index + 1) = decimal_point;
        let offset = 2 - kk;
        for i in 2..offset {
            *result.offset(index + i) = b'0';
        }
        write_mantissa_long(v.mantissa, result.offset(index + offset + length));
        index as usize + length as usize + offset as usize
    }
}

pub unsafe fn format64_fixed(f: f64, precision: usize, decimal_point: u8, result: *mut u8) -> usize {
    let bits = f.to_bits();
    let sign = ((bits >> (DOUBLE_MANTISSA_BITS + DOUBLE_EXPONENT_BITS)) & 1) != 0;
    let ieee_mantissa = bits & ((1u64 << DOUBLE_MANTISSA_BITS) - 1);
    let ieee_exponent =
        (bits >> DOUBLE_MANTISSA_BITS) as u32 & ((1u32 << DOUBLE_EXPONENT_BITS) - 1);

    let mut index = 0isize;
    if sign {
        *result = b'-';
        index += 1;
    }

    if ieee_exponent == 0 && ieee_mantissa == 0 {
        *result.offset(index) = b'0';
        if precision > 0 {
            *result.offset(index + 1) = b'.';
            for i in 0..precision as isize {
                *result.offset(index + 1 + i) = b'0';
            }
            return precision + 2 + usize::from(sign);
        } else {
            return 1 + usize::from(sign);
        }
    }

    let v = d2d(ieee_mantissa, ieee_exponent);

    let length = d2s::decimal_length17(v.mantissa) as isize;
    let k = v.exponent as isize;
    let kk = length + k; // 10^(kk-1) <= v < 10^kk
    debug_assert!(k >= -324);

    let mut round = Round::No;

    let mut written = if 0 <= k {
        // 1234e7 -> 12340000000.0
        write_mantissa_long(v.mantissa, result.offset(index + length));
        for i in length..kk {
            *result.offset(index + i) = b'0';
        }
        if precision > 0 {
            *result.offset(index + kk) = decimal_point;
            for i in 0..precision as isize {
                *result.offset(index + kk + 1 + i) = b'0';
            }
        }
        index as usize + kk as usize + usize::from(precision > 0) + precision
    } else if 0 < kk {
        // 1234e-2 -> 12.34
        let limit = (precision as isize + kk).min(length);
        write_mantissa_n_digits(limit as usize, length as usize, v.mantissa, result.offset(index + limit + 1));
        ptr::copy(result.offset(index + 1), result.offset(index), kk as usize);
        *result.offset(index + kk) = decimal_point;
        let trailing_zeros = (precision as isize + k).max(0);
        for i in 0..trailing_zeros {
            *result.offset(index + length + 1 + i) = b'0';
        }
        if trailing_zeros == 0 && limit > 0 && limit < length {
            let remainder = v.mantissa % 10u64.pow((length - limit) as u32);
            if remainder > 5u64.pow((length - limit) as u32 - 1) {
                round = Round::Up;
            }
        }
        index as usize + limit as usize + 1 + trailing_zeros as usize
    } else {
        // 1234e-6 -> 0.001234
        *result.offset(index) = b'0';
        if precision == 0 {
            if v.mantissa >= 5u64.pow(length as u32) {
                // Round here
                *result.offset(index) = b'1';
            }
            return index as usize + 1;
        }
        *result.offset(index + 1) = decimal_point;
        let offset = (2 - kk).min(precision as isize + 2);
        for i in 2..offset {
            *result.offset(index + i) = b'0';
        }
        let limit = (precision as isize + kk).max(0).min(length);
        write_mantissa_n_digits(limit as usize, length as usize, v.mantissa, result.offset(index + offset + limit));
        let trailing_zeros = (precision as isize - length - (offset - 2)).max(0);
        for i in 0..trailing_zeros {
            *result.offset(index + length + offset + i) = b'0';
        }
        if trailing_zeros == 0 && limit > 0 && limit < length {
            let remainder = v.mantissa % 10u64.pow((length - limit) as u32);
            if remainder > 5u64.pow((length - limit) as u32 - 1) {
                round = Round::Up;
            }
        }
        index as usize + limit as usize + offset as usize + trailing_zeros as usize
    };

    if round != Round::No {
        let mut round_index = written as isize;
        let mut dot_index = 0; // decimal can't be located at index 0
        loop {
            round_index -= 1;
            let c = *result.offset(round_index);
            if round_index == -1 || c == b'-' {
                *result.offset(round_index + 1) = b'1';
                if dot_index > 0 {
                    *result.offset(dot_index) = b'0';
                    *result.offset(dot_index + 1) = decimal_point;
                }
                *result.offset(index) = b'0';
                written += 1;
                break;
            }
            if c == decimal_point {
                dot_index = round_index;
                continue;
            } else if c == b'9' {
                *result.offset(round_index) = b'0';
                round = Round::Up;
                continue;
            } else {
                if round == Round::UpIfOdd && c % 2 == 0 {
                    break;
                }
                *result.offset(round_index) = c + 1;
                break;
            }
        }
    }

    return written;
}

#[repr(u8)]
#[derive(PartialEq, Eq)]
enum Round {
    No,
    Up,
    UpIfOdd,
}

/// Print f32 to the given buffer and return number of bytes written.
///
/// At most 16 bytes will be written.
///
/// ## Special cases
///
/// This function **does not** check for NaN or infinity. If the input
/// number is not a finite float, the printed representation will be some
/// correctly formatted but unspecified numerical value.
///
/// Please check [`is_finite`] yourself before calling this function, or
/// check [`is_nan`] and [`is_infinite`] and handle those cases yourself.
///
/// [`is_finite`]: https://doc.rust-lang.org/std/primitive.f32.html#method.is_finite
/// [`is_nan`]: https://doc.rust-lang.org/std/primitive.f32.html#method.is_nan
/// [`is_infinite`]: https://doc.rust-lang.org/std/primitive.f32.html#method.is_infinite
///
/// ## Safety
///
/// The `result` pointer argument must point to sufficiently many writable bytes
/// to hold Ryū's representation of `f`.
///
/// ## Example
///
/// ```
/// use std::{mem::MaybeUninit, slice, str};
///
/// let f = 1.234f32;
///
/// unsafe {
///     let mut buffer = [MaybeUninit::<u8>::uninit(); 16];
///     let len = ryu::raw::format32(f, buffer.as_mut_ptr() as *mut u8);
///     let slice = slice::from_raw_parts(buffer.as_ptr() as *const u8, len);
///     let print = str::from_utf8_unchecked(slice);
///     assert_eq!(print, "1.234");
/// }
/// ```
#[must_use]
#[cfg_attr(feature = "no-panic", no_panic)]
pub unsafe fn format32(f: f32, result: *mut u8) -> usize {
    let bits = f.to_bits();
    let sign = ((bits >> (FLOAT_MANTISSA_BITS + FLOAT_EXPONENT_BITS)) & 1) != 0;
    let ieee_mantissa = bits & ((1u32 << FLOAT_MANTISSA_BITS) - 1);
    let ieee_exponent = (bits >> FLOAT_MANTISSA_BITS) & ((1u32 << FLOAT_EXPONENT_BITS) - 1);

    let mut index = 0isize;
    if sign {
        *result = b'-';
        index += 1;
    }

    if ieee_exponent == 0 && ieee_mantissa == 0 {
        ptr::copy_nonoverlapping(b"0.0".as_ptr(), result.offset(index), 3);
        return sign as usize + 3;
    }

    let v = f2d(ieee_mantissa, ieee_exponent);

    let length = common::decimal_length9(v.mantissa) as isize;
    let k = v.exponent as isize;
    let kk = length + k; // 10^(kk-1) <= v < 10^kk
    debug_assert!(k >= -45);

    if 0 <= k && kk <= 13 {
        // 1234e7 -> 12340000000.0
        write_mantissa(v.mantissa, result.offset(index + length));
        for i in length..kk {
            *result.offset(index + i) = b'0';
        }
        *result.offset(index + kk) = b'.';
        *result.offset(index + kk + 1) = b'0';
        index as usize + kk as usize + 2
    } else if 0 < kk && kk <= 13 {
        // 1234e-2 -> 12.34
        write_mantissa(v.mantissa, result.offset(index + length + 1));
        ptr::copy(result.offset(index + 1), result.offset(index), kk as usize);
        *result.offset(index + kk) = b'.';
        index as usize + length as usize + 1
    } else if -6 < kk && kk <= 0 {
        // 1234e-6 -> 0.001234
        *result.offset(index) = b'0';
        *result.offset(index + 1) = b'.';
        let offset = 2 - kk;
        for i in 2..offset {
            *result.offset(index + i) = b'0';
        }
        write_mantissa(v.mantissa, result.offset(index + length + offset));
        index as usize + length as usize + offset as usize
    } else if length == 1 {
        // 1e30
        *result.offset(index) = b'0' + v.mantissa as u8;
        *result.offset(index + 1) = b'e';
        index as usize + 2 + write_exponent2(kk - 1, result.offset(index + 2))
    } else {
        // 1234e30 -> 1.234e33
        write_mantissa(v.mantissa, result.offset(index + length + 1));
        *result.offset(index) = *result.offset(index + 1);
        *result.offset(index + 1) = b'.';
        *result.offset(index + length + 1) = b'e';
        index as usize
            + length as usize
            + 2
            + write_exponent2(kk - 1, result.offset(index + length + 2))
    }
}
