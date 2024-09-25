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

#[macro_use]
mod macros;


use std::f64;
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaChaRng;
use ryu::d2fixed_buffered_n;

fn std_format(n: f64, sig_digits: usize, precision: usize, decimal_point: char) -> String {
    let tmp = format!("{:.1$}", n, precision);
    let mut split = tmp.split('.');
    let int_part = split.next().unwrap();
    let mut frac_part = split.next().map(|s| s.to_string());
    let int_len = int_part.len();
    let mut result = int_part
        .chars()
        .take(sig_digits)
        .chain(std::iter::repeat('0').take(int_len.saturating_sub(sig_digits as usize)))
        .collect::<String>();
    let mut sig_digits_remaining = sig_digits;
    if result != "0" {
        sig_digits_remaining = sig_digits_remaining.saturating_sub(int_len);
    }
    let leading_zeros = if result != "0" {
        0
    } else {
        frac_part.clone().map(|s| s.find(|c| c != '0')).flatten().unwrap_or_default()
    };
    // Special case; the std algorithm will round, but we want to truncate when
    // we've exhausted our significant digits
    if sig_digits_remaining + leading_zeros <= precision {
        let with_extra_precision = format!("{:.1$}", n, precision + 10);
        let mut split = with_extra_precision.split('.');
        let int_part = split.next().unwrap();
        let int_len = int_part.len();
        result = int_part
            .chars()
            .take(sig_digits)
            .chain(std::iter::repeat('0').take(int_len.saturating_sub(sig_digits)))
            .collect::<String>();
        frac_part = split.next().map(|s| s.to_string());
    }
    if let Some(part) = frac_part {
        let frac = part.to_string();
        let sig_index = frac.find(|c: char| c != '0');
        let sig_digits_remaining = if result == "0" {
            sig_digits + sig_index.unwrap_or_default()
        } else {
            sig_digits.saturating_sub(int_len)
        };
        let frac_part = match sig_index {
            Some(index) => std::iter::repeat('0')
                .take(index)
                .chain(frac.chars().skip(index))
                .take(sig_digits_remaining)
                .chain(std::iter::repeat('0'))
                .take(precision)
                .collect::<String>(),
            None => std::iter::repeat('0')
                .take(precision)
                .collect::<String>(),
        };
        if frac_part.len() > 0 {
            result.push(decimal_point);
            result.push_str(&frac_part);
        }
    }
    result
}

#[test]
fn prop_test() {
    let mut rng = thread_rng();
    let seed = rng.gen::<u64>();
    //let seed = 7672563757055851643;
    println!("seed = {seed}");
    let mut rng = ChaChaRng::seed_from_u64(seed);
    for _ in 0..1_000_000 {
        let n = rng.gen::<f64>();
        let e = rng.gen_range(-42..42);
        let n = n * 10.0f64.powi(e);
        dbg!(n);

        let precision = rng.gen_range(0..16);
        let precision = e.min(0).abs() as usize + precision;
        dbg!(precision);

        let decimal_point = if rng.gen_bool(0.5) { '.' } else { ',' };

        let std_format = std_format(n, f64::DIGITS as usize, precision, decimal_point);

        let mut buffer = [0u8; 2000];
        let len = d2fixed_buffered_n(n, precision, decimal_point as u8, &mut buffer[..]);
        let ryu_format = unsafe { std::str::from_utf8_unchecked(&buffer[0..len]) };
        assert_eq!(std_format, ryu_format);
    }
}
