use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{thread_rng, Rng};

use ryu::d2fixed_buffered_n;

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
            let written = d2fixed_buffered_n(*f, precision, &mut buf);
            let _formatted = unsafe { std::str::from_utf8_unchecked(&buf[0..written]) };
        }
    }

    let mut group = c.benchmark_group("d2fixed");
    for precision in 0..=15 {
        group.bench_with_input(
            BenchmarkId::new(&format!("precision {precision}"), &format!("{} floats", floats.len())),
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
