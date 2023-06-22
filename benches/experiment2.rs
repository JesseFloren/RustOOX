use criterion::{criterion_group, criterion_main, Criterion, SamplingMode, BenchmarkGroup, measurement::{Measurement, WallTime}};
use lib::{verify, Options, Heuristic};

fn options() -> Options<'static> {
    Options {
        k: 120,
        quiet: true,
        with_exceptional_clauses: true,
        heuristic: lib::Heuristic::DepthFirstSearch,
        visualize_heuristic: false,
        visualize_coverage: false,
        symbolic_array_size: 5,
        time_budget: 900,
        log_path: "./logs/log.txt",
        discard_logs: true,
        prune_path_z3: false,
        local_solving_threshold: Some(1000),
    }
}

fn experiment2<'a, M: Measurement>(c: &'a mut Criterion<M>) -> BenchmarkGroup<'a, M>{
    let mut options = options();
    let mut group = c.benchmark_group("experiment1");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);
    group.bench_function("List sorting functions --heuristic Depth First Search", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment2/list-sorting/sorting.oox"],
                "Main",
                "test",
                options,
            )
        })
    });
    options.heuristic = Heuristic::MinDist2Uncovered;
    group.bench_function("List sorting functions --heuristic Min Dist 2 Uncovered", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment2/list-sorting/sorting.oox"],
                "Main",
                "test",
                options,
            )
        })
    });
    options.heuristic = Heuristic::RandomPath;
    group.bench_function("List sorting functions --heuristic Random Path", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment2/list-sorting/sorting.oox"],
                "Main",
                "test",
                options,
            )
        })
    });

    options.heuristic = Heuristic::RoundRobinMD2URandomPath;
    group.bench_function("List sorting functions --heuristic Round Robin MD2U & Random Path", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment2/list-sorting/sorting.oox"],
                "Main",
                "test",
                options,
            )
        })
    });
    group
}


criterion_group!(benches, experiment2);
criterion_main!(benches);
