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

#[test]
fn prop_test() {
    let mut rng = thread_rng();
    let seed = rng.gen::<u64>();
    //let seed = 9629399966589211785;
    println!("seed = {seed}");
    for _ in 0..1_000_000 {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        let n = rng.gen::<f64>();
        let e = rng.gen_range(-42..42);
        let n = n * 10.0f64.powi(e);
        dbg!(n);

        let precision = rng.gen_range(0..16);
        let precision = e.min(0).abs() as usize + precision;
        dbg!(precision);

        let std_format = format!("{:.1$}", n, precision);
        let mut buffer = [0u8; 2000];
        let len = d2fixed_buffered_n(n, precision, &mut buffer[..]);
        let ryu_format = unsafe { std::str::from_utf8_unchecked(&buffer[0..len]) };
        dbg!(&buffer[0..len]);
        assert_eq!(std_format, ryu_format);
    }
}


