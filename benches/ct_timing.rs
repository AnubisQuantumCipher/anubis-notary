//! Constant-time timing tests using dudect methodology.
//!
//! This benchmark verifies that constant-time operations do not leak
//! information through timing side channels using statistical testing.
//!
//! The dudect methodology:
//! 1. Run the same operation on two classes of inputs
//! 2. Measure execution times for both classes
//! 3. Use Welch's t-test to detect statistical differences
//! 4. If |t-statistic| > threshold (typically 4.5), timing leak detected
//!
//! References:
//! - Reparaz, O., Balasch, J., & Verbauwhede, I. (2017).
//!   "Dude, is my code constant time?"
//! - https://github.com/oreparaz/dudect

use anubis_core::ct::{ct_eq, ct_lookup, ct_lt_u64, ct_select, ct_select_u64};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Instant;

/// Number of measurements per class for t-test
const MEASUREMENTS: usize = 10000;

/// T-statistic threshold for detecting timing leak
/// Values above 4.5 indicate statistically significant timing differences
const T_THRESHOLD: f64 = 4.5;

/// Run dudect-style test and return t-statistic
fn dudect_test<A, B, R>(class_a: A, class_b: B) -> f64
where
    A: Fn() -> R,
    B: Fn() -> R,
{
    let mut times_a = Vec::with_capacity(MEASUREMENTS);
    let mut times_b = Vec::with_capacity(MEASUREMENTS);

    // Interleave measurements to reduce systematic bias
    for _ in 0..MEASUREMENTS {
        // Measure class A
        let start = Instant::now();
        let _ = black_box(class_a());
        let elapsed_a = start.elapsed().as_nanos() as f64;
        times_a.push(elapsed_a);

        // Measure class B
        let start = Instant::now();
        let _ = black_box(class_b());
        let elapsed_b = start.elapsed().as_nanos() as f64;
        times_b.push(elapsed_b);
    }

    // Compute Welch's t-test statistic
    let n_a = times_a.len() as f64;
    let n_b = times_b.len() as f64;

    let mean_a: f64 = times_a.iter().sum::<f64>() / n_a;
    let mean_b: f64 = times_b.iter().sum::<f64>() / n_b;

    let var_a: f64 = times_a.iter().map(|x| (x - mean_a).powi(2)).sum::<f64>() / (n_a - 1.0);
    let var_b: f64 = times_b.iter().map(|x| (x - mean_b).powi(2)).sum::<f64>() / (n_b - 1.0);

    let stderr = (var_a / n_a + var_b / n_b).sqrt();

    if stderr < 1e-10 {
        0.0 // Avoid division by zero
    } else {
        (mean_a - mean_b) / stderr
    }
}

/// Test ct_eq with equal vs different inputs
fn test_ct_eq_timing() -> f64 {
    let equal_a = [0x42u8; 32];
    let equal_b = [0x42u8; 32];
    let diff_a = [0x00u8; 32];
    let diff_b = [0xFFu8; 32];

    dudect_test(|| ct_eq(&equal_a, &equal_b), || ct_eq(&diff_a, &diff_b))
}

/// Test ct_select with true vs false choice
fn test_ct_select_timing() -> f64 {
    dudect_test(
        || ct_select(true, 0xAA, 0x55) as u64,
        || ct_select(false, 0xAA, 0x55) as u64,
    )
}

/// Test ct_select_u64 with true vs false choice
fn test_ct_select_u64_timing() -> f64 {
    dudect_test(
        || ct_select_u64(true, 0xDEADBEEF, 0xCAFEBABE),
        || ct_select_u64(false, 0xDEADBEEF, 0xCAFEBABE),
    )
}

/// Test ct_lt_u64 with different comparison outcomes
fn test_ct_lt_u64_timing() -> f64 {
    dudect_test(
        || ct_lt_u64(5, 10), // a < b -> 1
        || ct_lt_u64(10, 5), // a > b -> 0
    )
}

/// Test ct_lookup at different indices
fn test_ct_lookup_timing() -> f64 {
    let table: [u64; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

    dudect_test(
        || ct_lookup(&table, 0),  // First element
        || ct_lookup(&table, 15), // Last element
    )
}

fn ct_timing_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("constant_time_verification");

    // Run timing tests and report results
    group.bench_function("ct_eq", |b| {
        b.iter(|| {
            let t = test_ct_eq_timing();
            assert!(
                t.abs() < T_THRESHOLD,
                "TIMING LEAK DETECTED in ct_eq: t={:.2} (threshold: {:.2})",
                t,
                T_THRESHOLD
            );
            black_box(t)
        })
    });

    group.bench_function("ct_select", |b| {
        b.iter(|| {
            let t = test_ct_select_timing();
            assert!(
                t.abs() < T_THRESHOLD,
                "TIMING LEAK DETECTED in ct_select: t={:.2} (threshold: {:.2})",
                t,
                T_THRESHOLD
            );
            black_box(t)
        })
    });

    group.bench_function("ct_select_u64", |b| {
        b.iter(|| {
            let t = test_ct_select_u64_timing();
            assert!(
                t.abs() < T_THRESHOLD,
                "TIMING LEAK DETECTED in ct_select_u64: t={:.2} (threshold: {:.2})",
                t,
                T_THRESHOLD
            );
            black_box(t)
        })
    });

    group.bench_function("ct_lt_u64", |b| {
        b.iter(|| {
            let t = test_ct_lt_u64_timing();
            assert!(
                t.abs() < T_THRESHOLD,
                "TIMING LEAK DETECTED in ct_lt_u64: t={:.2} (threshold: {:.2})",
                t,
                T_THRESHOLD
            );
            black_box(t)
        })
    });

    group.bench_function("ct_lookup", |b| {
        b.iter(|| {
            let t = test_ct_lookup_timing();
            assert!(
                t.abs() < T_THRESHOLD,
                "TIMING LEAK DETECTED in ct_lookup: t={:.2} (threshold: {:.2})",
                t,
                T_THRESHOLD
            );
            black_box(t)
        })
    });

    group.finish();
}

/// Print a summary report of all timing tests
#[allow(dead_code)]
fn print_timing_report() {
    println!("\n=== Constant-Time Verification Report ===\n");

    let tests = [
        ("ct_eq", test_ct_eq_timing()),
        ("ct_select", test_ct_select_timing()),
        ("ct_select_u64", test_ct_select_u64_timing()),
        ("ct_lt_u64", test_ct_lt_u64_timing()),
        ("ct_lookup", test_ct_lookup_timing()),
    ];

    println!("| Function       | t-statistic | Status |");
    println!("|----------------|-------------|--------|");

    let mut all_pass = true;
    for (name, t) in tests {
        let status = if t.abs() < T_THRESHOLD {
            "PASS"
        } else {
            all_pass = false;
            "FAIL"
        };
        println!("| {:<14} | {:>11.2} | {} |", name, t, status);
    }

    println!("\nThreshold: |t| < {:.1}", T_THRESHOLD);
    println!("Measurements per class: {}", MEASUREMENTS);

    if all_pass {
        println!("\n✓ All constant-time operations verified");
    } else {
        println!("\n✗ TIMING LEAKS DETECTED - review failed operations");
    }
}

criterion_group!(benches, ct_timing_benchmarks);
criterion_main!(benches);
