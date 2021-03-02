#![allow(unused_imports)]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use petgraph::{ Graph, Directed };
use graphalgs::shortest_path::{ apd, seidel, shortest_distances, floyd_warshall };
use graphalgs::generate::random_ungraph;
use graphalgs::adj_matrix::unweighted;


#[allow(unused_must_use)]
fn run(graph: &Graph::<(), f32, Directed, usize>) {
    seidel(&graph);
}


fn criterion_benchmark(c: &mut Criterion) {
    let n = 100;

    let graph = Graph::<(), f32, Directed, usize>::from_edges(
        random_ungraph(n, n*(n-1)/2).unwrap()
        .into_iter().map(|edge| (edge.0, edge.1, 1.0))
    );
    c.bench_function("Seidel", |b| b.iter(|| black_box(run(&graph))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
