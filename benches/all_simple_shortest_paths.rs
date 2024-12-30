use criterion::{black_box, criterion_group, measurement::WallTime, BenchmarkGroup, Criterion};
use graphalgs::shortest_path::{floyd_warshall, johnson, seidel, shortest_distances, spfa};
use petgraph::{
    algo::{bellman_ford, dijkstra, floyd_warshall as petgraph_floyd_warshall},
    graph::NodeIndex,
    visit::IntoNodeIdentifiers,
    Graph, Undirected,
};
use std::cmp::{max, min};

fn bench_all_simple_sp_100_dense(c: &mut Criterion) {
    let mut group = c.benchmark_group("All Shortest Paths: dense 100 nodes\n");
    group.sample_size(30);
    call_group(&mut group, 100, true);
    group.finish();
}

fn bench_all_simple_sp_1000_dense(c: &mut Criterion) {
    let mut group = c.benchmark_group("All Shortest Paths: dense 1000 nodes\n");
    group.sample_size(10);
    call_group(&mut group, 1000, true);
    group.finish();
}

fn bench_all_simple_sp_100_sparse(c: &mut Criterion) {
    let mut group = c.benchmark_group("All Shortest Paths: sparse 100 nodes\n");
    group.sample_size(30);
    call_group(&mut group, 100, false);
    group.finish();
}

fn bench_all_simple_sp_1000_sparse(c: &mut Criterion) {
    let mut group = c.benchmark_group("All Shortest Paths: sparse 1000 nodes\n");
    group.sample_size(10);
    call_group(&mut group, 1000, false);
    group.finish();
}

fn call_group(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    seidel_bench_helper(c, node_count, dense);
    fw_bench_helper(c, node_count, dense);
    petgraph_fw_bench_helper(c, node_count, dense);
    johnson_bench_helper(c, node_count, dense);
    n_bfs_bench_helper(c, node_count, dense);
    n_bellman_ford_bench_helper(c, node_count, dense);
    n_spfa_bench_helper(c, node_count, dense);
    n_dijkstra_bench_helper(c, node_count, dense);
}

fn seidel_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("Seidel", |b| {
        b.iter(|| {
            let output = seidel(&graph);
            black_box(output)
        })
    });
}

fn fw_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("Floyd-Warshall", |b| {
        b.iter(|| {
            let output = floyd_warshall(&graph, |_| 1.0);
            black_box(output)
        })
    });
}

fn petgraph_fw_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("Floyd-Warshall (petgraph)", |b| {
        b.iter(|| {
            let output = petgraph_floyd_warshall(&graph, |_| 1.0);
            black_box(output)
        })
    });
}

fn n_bfs_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("BFS n times", |b| {
        b.iter(|| {
            let mut output = Vec::with_capacity(node_count);
            for n in graph.node_identifiers() {
                output.push(shortest_distances(&graph, n));
            }
            black_box(output)
        })
    });
}

fn johnson_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("Johnson", |b| {
        b.iter(|| {
            let output = johnson(&graph, |_| 1.0);
            black_box(output)
        })
    });
}

fn n_bellman_ford_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("Bellman-Ford n times", |b| {
        b.iter(|| {
            let mut output = Vec::with_capacity(node_count);
            for n in graph.node_identifiers() {
                output.push(bellman_ford(&graph, n));
            }
            black_box(output)
        })
    });
}

fn n_spfa_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("SPFA n times", |b| {
        b.iter(|| {
            let mut output = Vec::with_capacity(node_count);
            for n in graph.node_identifiers() {
                output.push(spfa(&graph, n));
            }
            black_box(output)
        })
    });
}

fn n_dijkstra_bench_helper(c: &mut BenchmarkGroup<WallTime>, node_count: usize, dense: bool) {
    let graph = simple_graph(node_count, dense);
    c.bench_function("Dijkstra n times".to_string(), |b| {
        b.iter(|| {
            let mut output = Vec::with_capacity(node_count);
            for n in graph.node_identifiers() {
                output.push(dijkstra(&graph, n, None, |_| 1.0));
            }
            black_box(output)
        })
    });
}

#[allow(clippy::needless_range_loop)]
fn simple_graph(node_count: usize, dense: bool) -> Graph<usize, f32, Undirected> {
    let mut graph = Graph::new_undirected();
    let nodes: Vec<NodeIndex<_>> = (0..node_count).map(|i| graph.add_node(i)).collect();
    for i in 0..node_count {
        let n1 = nodes[i];
        let neighbour_count = if dense {
            i % (node_count / 3) + 3
        } else {
            i % 8 + 3
        };
        let j_from = max(0, i as i32 - neighbour_count as i32 / 2) as usize;
        let j_to = min(node_count, j_from + neighbour_count);
        for j in j_from..j_to {
            let n2 = nodes[j];
            let distance = 1.0;
            graph.add_edge(n1, n2, distance);
        }
    }
    graph
}

criterion_group!(
    all_simple_shortest_paths,
    bench_all_simple_sp_100_dense,
    bench_all_simple_sp_1000_dense,
    bench_all_simple_sp_100_sparse,
    bench_all_simple_sp_1000_sparse
);
