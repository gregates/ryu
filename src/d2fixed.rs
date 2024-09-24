// Translated from C to Rust. The original C code can be found at
// https://github.com/ulfjack/ryu and carries the following license:
//
// Copyright 2018 Ulf Adams
//
// The contents of this file may be used under the terms of the Apache License,
// Version 2.0.
//
//    (See accompanying file LICENSE-Apache or copy at
//     http://www.apache.org/licenses/LICENSE-2.0)
//
// Alternatively, the contents of this file may be used under the terms of
// the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE-Boost or copy at
//     https://www.boost.org/LICENSE_1_0.txt)
//
// Unless required by applicable law or agreed to in writing, this software
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.

use crate::common::{decimal_length9, log10_pow2};
use crate::digit_table::DIGIT_TABLE;
use crate::d2fixed_full_table::{ADDITIONAL_BITS_2, MIN_BLOCK_2, POW10_OFFSET, POW10_OFFSET_2, POW10_SPLIT, POW10_SPLIT_2};
use crate::d2s_intrinsics::multiple_of_power_of_2;

pub const DOUBLE_MANTISSA_BITS: u32 = 52;
pub const DOUBLE_EXPONENT_BITS: u32 = 11;
pub const DOUBLE_BIAS: i32 = 1023;
pub const POW10_ADDITIONAL_BITS: usize = 120;

#[cfg_attr(feature = "no-panic", inline)]
fn umul256(a: u128, b_hi: u64, b_lo: u64) -> (u128, u128) {
    let a_lo = a as u64;
    let a_hi = (a >> 64) as u64;

    let b00 = a_lo as u128 * b_lo as u128;
    let b01 = a_lo as u128 * b_hi as u128;
    let b10 = a_hi as u128 * b_lo as u128;
    let b11 = a_hi as u128 * b_hi as u128;

    let b00_lo = b00 as u64;
    let b00_hi = (b00 >> 64) as u64;

    let mid1 = b10 + b00_hi as u128;
    let mid1_lo = mid1 as u64;
    let mid1_hi = (mid1 >> 64) as u64;

    let mid2 = b01 + mid1_lo as u128;
    let mid2_lo = mid2 as u64;
    let mid2_hi = (mid2 >> 64) as u64;

    let p_hi = b11 + mid1_hi as u128 + mid2_hi as u128;
    let p_lo = ((mid2_lo as u128) << 64) | b00_lo as u128;

    (p_hi, p_lo)
}

// Returns the high 128 bits of the 256-bit product of a and b
#[cfg_attr(feature = "no-panic", inline)]
fn umul256_hi(a: u128, b_hi: u64, b_lo: u64) -> u128 {
    umul256(a, b_hi, b_lo).0
}

// Unfortunately, gcc/clang do not automatically turn a 128-bit integer division
// into a multiplication, so we have to do it manually.
#[cfg_attr(feature = "no-panic", inline)]
fn u128_mod1e9(v: u128) -> u32 {
    // After multiplying, we're going to shift right by 29, then truncate to u32.
    // This means that we need only 29 + 32 = 61 bits, so we can truncate to u64 before shifting.
    let multiplied = umul256_hi(v, 0x89705F4136B4A597, 0x31680A88F8953031) as u64;

    // For u32 truncation, see the mod1e9 comment in d2s_instrinsics
    let shifted = (multiplied >> 29) as u32;

    (v as u32).overflowing_sub(1000000000u32.overflowing_mul(shifted).0).0
}

// Best case: use 128-bit type
#[cfg_attr(feature = "no-panic", inline)]
fn mul_shift_mod1e9(m: u64, mul: &[u64; 3], j: i32) -> u32 {
    let b0 = m as u128 * mul[0] as u128; // 0
    let b1 = m as u128 * mul[1] as u128; // 64
    let b2 = m as u128 * mul[2] as u128; // 128
    debug_assert!(j >= 128);
    debug_assert!(j <= 180);
    // j: [128, 256)
    let mid = b1 + (b0 >> 64); // 64
    let s1 = b2 + (mid >> 64); // 128
    u128_mod1e9(s1 >> (j - 128))
}

// Convert `digits` to a sequence of decimal digits. Append the digits to the result.
// The caller has to guarantee that:
//   10^(olength-1) <= digits < 10^olength
// e.g., by passing `olength` as `decimalLength9(digits)`.
#[cfg_attr(feature = "no-panic", inline)]
fn append_n_digits(olength: usize, mut digits: usize, result: &mut [u8]) {
    let mut i = 0;
    while digits >= 10_000 {
        let c = digits % 10_000;
        digits /= 10_000;
        let c0 = (c % 100) << 1;
        let c1 = (c / 100) << 1;
        let dest = &mut result[olength - i - 2..olength - i];
        dest.copy_from_slice(&DIGIT_TABLE[c0..c0+2]);
        let dest = &mut result[olength - i - 4..olength - i - 2];
        dest.copy_from_slice(&DIGIT_TABLE[c1..c1+2]);
        i += 4;
    }
    if digits >= 100 {
        let c = (digits % 100) << 1;
        digits /= 100;
        let dest = &mut result[olength - i - 2..olength - i];
        dest.copy_from_slice(&DIGIT_TABLE[c..c+2]);
        i += 2;
    }
    if digits >= 10 {
        let c = digits << 1;
        let dest = &mut result[olength - i - 2..olength - i];
        dest.copy_from_slice(&DIGIT_TABLE[c..c+2]);
    } else {
        result[0] = b'0' + digits as u8;
    }
}

// Convert `digits` to decimal and write the last `count` decimal digits to result.
// If `digits` contains additional digits, then those are silently ignored.
#[cfg_attr(feature = "no-panic", inline)]
fn append_c_digits(count: usize, mut digits: usize, result: &mut [u8]) {
    // Copy pairs of digits from DIGIT_TABLE.
    let mut i = 0;
    while i < count - 1 {
        let c = (digits % 100) << 1;
        digits /= 100;
        let dest = &mut result[count - i - 2..count - i];
        dest.copy_from_slice(&DIGIT_TABLE[c..c+2]);
        i += 2;
    }
    // Generate the last digit if count is odd.
    if i < count {
        let c = b'0' + (digits % 10) as u8;
        result[count - i - 1] = c;
    }
}

// Convert `digits` to decimal and write the last 9 decimal digits to result.
// If `digits` contains additional digits, then those are silently ignored.
#[cfg_attr(feature = "no-panic", inline)]
fn append_9_digits(mut digits: usize, result: &mut [u8]) {
    if digits == 0 {
        let dest = &mut result[0..9];
        dest.fill(b'0');
        return;
    }

    let mut i = 0;
    while i < 5 {
        let c = digits % 10_000;
        digits /= 10_000;
        let c0 = (c % 100) << 1;
        let c1 = (c / 100) << 1;
        let dest = &mut result[7-i..9-i];
        dest.copy_from_slice(&DIGIT_TABLE[c0..c0+2]);
        let dest = &mut result[5-i..7-i];
        dest.copy_from_slice(&DIGIT_TABLE[c1..c1+2]);
        i += 4;
    }
    result[0] = b'0' + digits as u8;
}

#[cfg_attr(feature = "no-panic", inline)]
fn index_for_exponent(e: usize) -> usize {
    (e + 15) / 16
}

#[cfg_attr(feature = "no-panic", inline)]
fn pow10_bits_for_index(idx: usize) -> usize {
    16 * idx + POW10_ADDITIONAL_BITS
}

#[cfg_attr(feature = "no-panic", inline)]
fn length_for_index(idx: usize) -> u32 {
    // +1 for ceil, +16 for mantissa, +8 to round up when dividing by 9
    (log10_pow2(16 * idx as i32) + 1 + 16 + 8) / 9
}

#[cfg_attr(feature = "no-panic", inline)]
fn copy_special_str_printf(result: &mut [u8], sign: bool, mantissa: u64) -> usize {
    if mantissa > 0 {
        let dest = &mut result[0..3];
        dest.copy_from_slice("nan".as_bytes());
        return 3;
    }
    if sign {
        result[0] = b'-';
    }
    let dest = &mut result[usize::from(sign)..8 + usize::from(sign)];
    dest.copy_from_slice("Infinity".as_bytes());
    8 + usize::from(sign)
}

pub fn d2fixed_buffered_n(d: f64, precision: usize, result: &mut [u8]) -> usize {
    let bits = d.to_bits();

    // Decode bits into sign, mantissa, and exponent.
    let ieee_sign = ((bits >> (DOUBLE_MANTISSA_BITS + DOUBLE_EXPONENT_BITS)) & 1) != 0;
    let ieee_mantissa = bits & ((1u64 << DOUBLE_MANTISSA_BITS) - 1);
    let ieee_exponent = ((bits >> DOUBLE_MANTISSA_BITS) & ((1 << DOUBLE_EXPONENT_BITS) - 1)) as u32;

    // Case distinction; exit early for the easy cases.
    if ieee_exponent == ((1 << DOUBLE_EXPONENT_BITS - 1)) {
        return copy_special_str_printf(result, ieee_sign, ieee_mantissa);
    }
    if ieee_exponent == 0 && ieee_mantissa == 0 {
        if ieee_sign {
            result[0] = b'-';
        }
        result[1] = b'0';
        if precision > 0 {
            result[2] = b'.';
            let dest = &mut result[3..3 + precision as usize];
            dest.fill(b'0');
        }
        return precision + 2 + usize::from(precision > 0);
    }

    let (e2, m2) = if ieee_exponent == 0 {
        (
            1 - DOUBLE_BIAS - DOUBLE_MANTISSA_BITS as i32,
            ieee_mantissa
        )
    } else {
        (
            ieee_exponent as i32 - DOUBLE_BIAS - DOUBLE_MANTISSA_BITS as i32,
            (1u64 << DOUBLE_MANTISSA_BITS) | ieee_mantissa
        )
    };

    let mut index = 0;
    let mut nonzero = false;
    if ieee_sign {
        result[index] = b'-';
        index += 1;
    }
    if e2 >= -52 {
        let idx = if e2 < 0 { 0 } else { index_for_exponent(e2 as usize) };
        let p10_bits = pow10_bits_for_index(idx);
        let len = length_for_index(idx) as i32;
        for i in (0..len).rev() {
            let j = (p10_bits as i32 - e2) as usize;
            // Temporary: j is usually around 128, and by shifting a bit, we push it to 128 or above, which is
            // a slightly faster code path in mulShift_mod1e9. Instead, we can just increase the multipliers.
            let digits = mul_shift_mod1e9(m2 << 8, &POW10_SPLIT[POW10_OFFSET[idx] as usize + i as usize], j as i32 + 8);
            if nonzero {
                append_9_digits(digits as usize, &mut result[index..]);
                index += 9;
            } else if digits != 0 {
                let olength = decimal_length9(digits) as usize;
                append_n_digits(olength, digits as usize, &mut result[index..]);
                index += olength;
                nonzero = true;
            }
        }
    }

    if !nonzero {
        result[index] = b'0';
        index += 1;
    }
    if precision > 0 {
        result[index] = b'.';
        index += 1;
    }

    if e2 < 0 {
        let idx = -e2 / 16;
        let blocks = precision / 9 + 1;
        // 0 = don't round up; 1 = round up unconditionally; 2 = round up if odd.
        let mut round_up = 0;
        let mut i = 0;
        if blocks <= MIN_BLOCK_2[idx as usize].into() {
            i = blocks;
            let dest = &mut result[index..index + precision];
            dest.fill(b'0');
            index += precision;
        } else if i < MIN_BLOCK_2[idx as usize].into() {
            i = MIN_BLOCK_2[idx as usize] as usize;
            let dest = &mut result[index..index + 9 * i];
            dest.fill(b'0');
            index += 9 * i;
        }
        while i < blocks {
            let j = ADDITIONAL_BITS_2 + (-e2 - 16 * idx);
            let p = POW10_OFFSET_2[idx as usize] as usize + i - MIN_BLOCK_2[idx as usize] as usize;
            if p >= POW10_OFFSET_2[idx as usize + 1] as usize {
                // If the remaining digits are all 0, then we might as well use memset.
                // No rounding required in this case.
                let fill = precision - 9 * i;
                let dest = &mut result[index..index + fill];
                dest.fill(b'0');
                break;
            }
            // Temporary: j is usually around 128, and by shifting a bit, we push it to 128 or above, which is
            // a slightly faster code path in mulShift_mod1e9. Instead, we can just increase the multipliers.
            let mut digits = mul_shift_mod1e9(m2 << 8, &POW10_SPLIT_2[p], j + 8);
            if i < blocks - 1 {
                append_9_digits(digits as usize, &mut result[index..]);
                index += 9;
            } else {
                let maximum = precision - 9 * i;
                let mut last_digit = 0;
                for _ in 0..9 - maximum {
                    last_digit = digits % 10;
                    digits /= 10;
                }
                if last_digit != 5 {
                    round_up = usize::from(last_digit > 5);
                } else {
                    // Is m * 10^(additionalDigits + 1) / 2^(-e2) integer?
                    let required_twos = -e2 - precision as i32 - 1;
                    let trailing_zeros = (required_twos <= 0) || (required_twos < 60 && multiple_of_power_of_2(m2, required_twos as u32));
                    round_up = if trailing_zeros { 2 } else { 1 };
                }
                if maximum > 0 {
                    append_c_digits(maximum, digits as usize, &mut result[index..]);
                    index += maximum;
                }
                break;
            }
            i += 1;
        }
        if round_up != 0 {
            let mut round_index = index as i32;
            let mut dot_index = 0; // '.' can't be located at index 0
            loop {
                round_index -= 1;
                if round_index == -1 || result[round_index as usize] == b'-' {
                    result[round_index as usize + 1] = b'1';
                    if dot_index > 0 {
                        result[dot_index] = b'0';
                        result[dot_index + 1] = b'.';
                    }
                    result[index] = b'0';
                    index += 1;
                    break;
                }
                let c = result[round_index as usize];
                if c == b'.' {
                    dot_index = round_index as usize;
                    continue;
                } else if c == b'9' {
                    result[round_index as usize] = b'0';
                    round_up = 1;
                    continue;
                } else {
                    if round_up == 2 && c % 2 == 0 {
                        break;
                    }
                    result[round_index as usize] = c + 1;
                    break;
                }
            }
        }
    } else {
        let dest = &mut result[index..index + precision];
        dest.fill(b'0');
        index += precision;
    }
    return index;
}
