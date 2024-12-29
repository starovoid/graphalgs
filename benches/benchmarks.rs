mod shortest_path;

use criterion::measurement::WallTime;
use criterion::BenchmarkGroup;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use graphalgs::elementary_circuits::elementary_circuits;
use graphalgs::generate::random_digraph;
use petgraph::{Directed, Graph};
use shortest_path::*;

fn elementary_circuits_helper(
    group: &mut BenchmarkGroup<WallTime>,
    name: &str,
    nodes: usize,
    nedges: usize,
) {
    group.bench_function(name, |b| {
        b.iter(|| {
            let graph: Graph<(), (), Directed, usize> =
                Graph::from_edges(random_digraph(nodes, nedges).unwrap());
            let output = elementary_circuits(&graph);
            black_box(output)
        })
    });
}

fn bench_elementary_circuits(c: &mut Criterion) {
    let mut group = c.benchmark_group("ElementaryCircuits");
    group.sample_size(10);
    elementary_circuits_helper(&mut group, "ManyNodes", 10000, 5000);
    let n = 14;
    elementary_circuits_helper(&mut group, "FewNodes", n, n * n / 2);
    group.finish();
}

criterion_group!(benches, bench_elementary_circuits);
criterion_main!(benches, shortest_path);
