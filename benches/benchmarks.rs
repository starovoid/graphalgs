#![allow(unused_imports)]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use graphalgs::adj_matrix::unweighted;
use graphalgs::generate::random_ungraph;
use graphalgs::shortest_path::{apd, floyd_warshall, seidel, shortest_distances};
use petgraph::{Directed, Graph};

#[allow(unused_must_use)]
fn run(graph: &Graph<(), f32, Directed, usize>) {
    seidel(&graph);
}

fn criterion_benchmark(c: &mut Criterion) {
    let n = 100;

    let graph = Graph::<(), f32, Directed, usize>::from_edges(
        random_ungraph(n, n * (n - 1) / 2)
            .unwrap()
            .into_iter()
            .map(|edge| (edge.0, edge.1, 1.0)),
    );
    c.bench_function("Seidel", |b| b.iter(|| black_box(run(&graph))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
