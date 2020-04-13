use criterion::{
    black_box,
    criterion_group,
    criterion_main,
    BatchSize,
    Bencher,
    Criterion,
    Throughput,
};
use hierarchical_hash_wheel_timer::{wheels::*, IdOnlyTimerEntry};
use rand::prelude::*;
use std::{rc::Rc, time::Duration};
use uuid::Uuid;

const NUM_ELEMENTS: usize = 10000;

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("wheel-throughput");
    group.throughput(Throughput::Elements(NUM_ELEMENTS as u64));
    group.bench_function("write-only-dense", write_only_dense_bench);
    group.bench_function("write-only-uniform", write_only_uniform_bench);
    group.bench_function(
        "write-only-uniform-with-overflow",
        write_only_uniform_with_overflow_bench,
    );
    group.bench_function("write-only-single", write_only_single_bench);
    group.bench_function("read-only", read_only_bench);
    group.bench_function("read-only-single", read_only_single_bench);
    group.bench_function("read-write", read_write_bench);
    group.finish();
}

fn write_only_dense_bench(bencher: &mut Bencher) -> () {
    bencher.iter_batched(
        || {
            let timer: QuadWheelWithOverflow<IdOnlyTimerEntry> = QuadWheelWithOverflow::new();
            let mut entries = Vec::with_capacity(NUM_ELEMENTS);
            for i in 1..=NUM_ELEMENTS {
                let id = Uuid::new_v4();
                let entry = IdOnlyTimerEntry {
                    id,
                    delay: Duration::from_millis(i as u64),
                };
                entries.push(entry);
            }
            (timer, entries)
        },
        |input| {
            let (mut timer, entries) = input;
            for entry in entries {
                let _ = timer.insert(entry);
            }
            timer
        },
        BatchSize::PerIteration,
    );
}

fn write_only_uniform_bench(bencher: &mut Bencher) -> () {
    bencher.iter_batched(
        || {
            let timer: QuadWheelWithOverflow<IdOnlyTimerEntry> = QuadWheelWithOverflow::new();
            let mut entries = Vec::with_capacity(NUM_ELEMENTS);
            let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
            for _i in 1..=NUM_ELEMENTS {
                let id = Uuid::new_v4();
                let mut delay: u32 = rng.gen();
                if delay == 0 {
                    // make sure the entry is actually inserted and not just returned immediately
                    delay = 1;
                }
                let entry = IdOnlyTimerEntry {
                    id,
                    delay: Duration::from_millis(delay as u64),
                };
                entries.push(entry);
            }
            (timer, entries)
        },
        |input| {
            let (mut timer, entries) = input;
            for entry in entries {
                let _ = timer.insert(entry);
            }
            timer
        },
        BatchSize::PerIteration,
    );
}

fn write_only_uniform_with_overflow_bench(bencher: &mut Bencher) -> () {
    bencher.iter_batched(
        || {
            let timer: QuadWheelWithOverflow<IdOnlyTimerEntry> = QuadWheelWithOverflow::new();
            let mut entries = Vec::with_capacity(NUM_ELEMENTS);
            let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(42);
            for _i in 1..=NUM_ELEMENTS {
                let id = Uuid::new_v4();
                let mut delay: u64 = rng.gen();
                if delay == 0 {
                    // make sure the entry is actually inserted and not just returned immediately
                    delay = 1;
                }
                let entry = IdOnlyTimerEntry {
                    id,
                    delay: Duration::from_millis(delay),
                };
                entries.push(entry);
            }
            (timer, entries)
        },
        |input| {
            let (mut timer, entries) = input;
            for entry in entries {
                let _ = timer.insert(entry);
            }
            timer
        },
        BatchSize::PerIteration,
    );
}

fn write_only_single_bench(bencher: &mut Bencher) -> () {
    bencher.iter_batched(
        || {
            let timer: QuadWheelWithOverflow<IdOnlyTimerEntry> = QuadWheelWithOverflow::new();
            let mut entries = Vec::with_capacity(NUM_ELEMENTS);
            for _i in 1..=NUM_ELEMENTS {
                let id = Uuid::new_v4();
                let entry = IdOnlyTimerEntry {
                    id,
                    delay: Duration::from_millis(1),
                };
                entries.push(entry);
            }
            (timer, entries)
        },
        |input| {
            let (mut timer, entries) = input;
            for entry in entries {
                let _ = timer.insert(entry);
            }
            timer
        },
        BatchSize::PerIteration,
    );
}

fn read_only_bench(bencher: &mut Bencher) -> () {
    bencher.iter_batched(
        || {
            let mut timer: QuadWheelWithOverflow<IdOnlyTimerEntry> = QuadWheelWithOverflow::new();
            for i in 1..=NUM_ELEMENTS {
                let id = Uuid::new_v4();
                let entry = IdOnlyTimerEntry {
                    id,
                    delay: Duration::from_millis(i as u64),
                };
                timer.insert(entry).unwrap();
            }
            timer
        },
        |mut timer| {
            for _i in 1..=NUM_ELEMENTS {
                let res = timer.tick();
                for rc_e in res {
                    match Rc::try_unwrap(rc_e) {
                        Ok(e) => drop(e),
                        Err(_) => (),
                    }
                }
            }
            timer
        },
        BatchSize::PerIteration,
    );
}

fn read_only_single_bench(bencher: &mut Bencher) -> () {
    bencher.iter_batched(
        || {
            let mut timer: QuadWheelWithOverflow<IdOnlyTimerEntry> = QuadWheelWithOverflow::new();
            for _i in 1..=NUM_ELEMENTS {
                let id = Uuid::new_v4();
                let entry = IdOnlyTimerEntry {
                    id,
                    delay: Duration::from_millis(1),
                };
                timer.insert(entry).unwrap();
            }
            timer
        },
        |mut timer| {
            let res = timer.tick();
            for rc_e in res {
                match Rc::try_unwrap(rc_e) {
                    Ok(e) => drop(e),
                    Err(_) => (),
                }
            }
            timer
        },
        BatchSize::PerIteration,
    );
}

fn read_write_bench(bencher: &mut Bencher) -> () {
    let id = Uuid::new_v4();
    let entry = IdOnlyTimerEntry {
        id,
        delay: Duration::from_millis(1),
    };
    let entry_rc = Rc::new(entry);
    bencher.iter_batched(
        || {
            let timer: QuadWheelWithOverflow<IdOnlyTimerEntry> = QuadWheelWithOverflow::new();
            timer
        },
        move |mut timer| {
            for _i in 1..=NUM_ELEMENTS {
                let _ = timer.insert_ref(entry_rc.clone());
                let res = timer.tick();
                for rc_e in res {
                    drop(rc_e);
                }
            }
            timer
        },
        BatchSize::PerIteration,
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
