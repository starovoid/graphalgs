#![allow(unused_imports)]
use criterion::measurement::WallTime;
use criterion::BenchmarkGroup;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use graphalgs::adj_matrix::unweighted;
use graphalgs::elementary_circuits::elementary_circuits;
use graphalgs::generate::{random_digraph, random_ungraph};
use graphalgs::shortest_path::{apd, floyd_warshall, seidel, shortest_distances};
use petgraph::{Directed, Graph};

#[allow(unused_must_use)]
fn run(graph: &Graph<(), f32, Directed, usize>) {
    seidel(graph);
}

fn bench_seidel(c: &mut Criterion) {
    let n = 100;
    let graph = Graph::<(), f32, Directed, usize>::from_edges(
        random_ungraph(n, n * (n - 1) / 2)
            .unwrap()
            .into_iter()
            .map(|edge| (edge.0, edge.1, 1.0)),
    );
    c.bench_function("Seidel", |b| b.iter(|| {
        run(&graph);
        black_box(())
    }));
}

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

criterion_group!(benches, bench_seidel, bench_elementary_circuits);
criterion_main!(benches);
