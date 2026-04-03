use std::collections::VecDeque;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use tinyvecdeq::arrayvecdeq::ArrayVecDeq;
fn bench_push_back_100(b: &mut Criterion) {
    let mut deq = ArrayVecDeq::<[_; 128]>::new();
    let mut b = b.benchmark_group("push back");
    b.bench_function("push back", |b| {
        b.iter(|| {
            for i in 0..100 {
                deq.push_back(i);
            }
            std::hint::black_box(&deq);
            deq.clear();
        })
    });
    let mut deq = VecDeque::with_capacity(128);
    b.bench_function("push back vecdeque", |b| {
        b.iter(|| {
            for i in 0..100 {
                deq.push_back(i);
            }
            std::hint::black_box(&deq);
            deq.clear();
        })
    });
    b.finish();
}

fn bench_push_front_100(b: &mut Criterion) {
    let mut deq = ArrayVecDeq::<[_; 128]>::new();
    let mut b = b.benchmark_group("push front");
    b.bench_function("push front", |b| {
        b.iter(|| {
            for i in 0..100 {
                deq.push_front(i);
            }
            deq.clear();
        })
    });
    let mut deq = VecDeque::with_capacity(128);
    b.bench_function("push front vecdeque", |b| {
        b.iter(|| {
            for i in 0..100 {
                deq.push_front(i);
            }
            deq.clear();
        })
    });
}

fn bench_pop_back_100(b: &mut Criterion) {
    let size = 100;
    let mut deq = ArrayVecDeq::<[_; 128]>::new();
    deq.extend(1..size);

    b.bench_function("pop back", |b| {
        b.iter_batched_ref(
            || deq.clone(),
            |deq| {
                while !deq.is_empty() {
                    std::hint::black_box(deq.pop_back());
                }
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_retain_whole_100(b: &mut Criterion) {
    let size = 100;
    let mut deq = ArrayVecDeq::<[_; 128]>::new();
    deq.extend(1..size);

    b.bench_function("retain whole", |b| {
        b.iter_batched_ref(
            || deq.clone(),
            |deq| {
                deq.retain(|x| *x > 0);
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_retain_odd_100(b: &mut Criterion) {
    let size = 100;
    let mut deq = ArrayVecDeq::<[_; 128]>::new();
    deq.extend(1..size);

    b.bench_function("retain odd", |b| {
        b.iter_batched_ref(
            || deq.clone(),
            |deq| {
                deq.retain(|x| x & 1 == 0);
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_retain_half_100(b: &mut Criterion) {
    let size = 100;
    let mut deq = ArrayVecDeq::<[_; 128]>::new();
    deq.extend(1..size);

    b.bench_function("retain half", |b| {
        b.iter_batched_ref(
            || deq.clone(),
            |deq| {
                deq.retain(|x| *x > size / 2);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(
    benches,
    bench_push_back_100,
    bench_push_front_100,
    bench_pop_back_100,
    bench_retain_whole_100,
    bench_retain_odd_100,
    bench_retain_half_100
);
criterion_main!(benches);
