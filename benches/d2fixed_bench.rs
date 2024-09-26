use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{thread_rng, Rng};

use ryu::raw::format64_fixed;
use std::io::Write;

pub fn d2fixed_bench(c: &mut Criterion) {
    let mut rng = thread_rng();
    let floats = (0..1_000_000)
        .map(|_| {
            let f = rng.gen::<f64>();
            let e = rng.gen_range(-20..21);
            f * 10.0f64.powi(e)
        })
        .collect::<Vec<_>>();

    fn format_all(precision: usize, floats: &[f64]) {
        let mut buf = [0u8; 1024];
        for f in floats {
            let written = unsafe { format64_fixed(*f, precision, b'.', buf.as_mut_ptr()) };
            let _formatted = unsafe { std::str::from_utf8_unchecked(&buf[0..written]) };
        }
    }

    fn format_all_std(precision: usize, floats: &[f64]) {
        let mut buf = [0u8; 1024];
        for f in floats {
            let _ = write!(&mut buf[..], "{:.1$}", f, precision);
        }
    }

    let mut group = c.benchmark_group("fixed precision");
    group.measurement_time(std::time::Duration::from_secs(20));
    for precision in 0..=15 {
        group.bench_with_input(
            BenchmarkId::new(&format!("std, precision {precision}"), &format!("{} floats", floats.len())),
            &floats,
            |b, floats| {
                b.iter(|| {
                    format_all_std(precision, floats);
                });
            },
        );
        group.bench_with_input(
            BenchmarkId::new(&format!("ryu, precision {precision}"), &format!("{} floats", floats.len())),
            &floats,
            |b, floats| {
                b.iter(|| {
                    format_all(precision, floats);
                });
            },
        );
    }
}

criterion_group!(benches, d2fixed_bench);
criterion_main!(benches);
