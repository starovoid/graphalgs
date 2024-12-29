use criterion::{black_box, criterion_group, Criterion};
use graphalgs::shortest_path::{floyd_warshall, seidel};
use petgraph::{
    algo::floyd_warshall as petgraph_floyd_warshall, graph::NodeIndex, Graph, Undirected,
};
use std::cmp::{max, min};

pub fn bench_seidel_simple_graph_100(c: &mut Criterion) {
    seidel_bench_helper(c, 100);
}

pub fn bench_petgraph_fw_simple_graph_100(c: &mut Criterion) {
    fw_bench_helper(c, 100);
}

pub fn bench_fw_simple_graph_100(c: &mut Criterion) {
    fw_bench_helper(c, 100);
}

pub fn bench_seidel_simple_graph_1000(c: &mut Criterion) {
    seidel_bench_helper(c, 1000);
}

pub fn bench_petgraph_fw_simple_graph_1000(c: &mut Criterion) {
    petgraph_fw_bench_helper(c, 1000);
}

pub fn bench_fw_simple_graph_1000(c: &mut Criterion) {
    fw_bench_helper(c, 1000);
}

pub fn seidel_bench_helper(c: &mut Criterion, node_count: usize) {
    let graph = simple_graph(node_count);
    c.bench_function(
        &format!("Seidel - Simple Graph - {node_count} nodes"),
        |b| {
            b.iter(|| {
                let output = seidel(&graph);
                black_box(output)
            })
        },
    );
}

fn fw_bench_helper(c: &mut Criterion, node_count: usize) {
    let graph = simple_graph(node_count);
    c.bench_function(
        &format!("Floyd-Warshall - Simple Graph - {node_count} nodes"),
        |b| {
            b.iter(|| {
                let output = floyd_warshall(&graph, |_| 1.0);
                black_box(output)
            })
        },
    );
}

pub fn petgraph_fw_bench_helper(c: &mut Criterion, node_count: usize) {
    let graph = simple_graph(node_count);
    c.bench_function(
        &format!("Floyd-Warshall (petgraph) - Simple Graph - {node_count} nodes"),
        |b| {
            b.iter(|| {
                let output = petgraph_floyd_warshall(&graph, |_| 1.0);
                black_box(output)
            })
        },
    );
}

fn simple_graph(node_count: usize) -> Graph<usize, usize, Undirected> {
    let mut graph = Graph::new_undirected();
    let nodes: Vec<NodeIndex<_>> = (0..node_count).map(|i| graph.add_node(i)).collect();
    for i in 0..node_count {
        let n1 = nodes[i];
        let neighbour_count = i % 8 + 3;
        let j_from = max(0, i as i32 - neighbour_count as i32 / 2) as usize;
        let j_to = min(node_count, j_from + neighbour_count);
        for j in j_from..j_to {
            let n2 = nodes[j];
            let distance = 1;
            graph.add_edge(n1, n2, distance);
        }
    }
    graph
}

criterion_group!(
    shortest_path,
    bench_seidel_simple_graph_100,
    bench_petgraph_fw_simple_graph_100,
    bench_fw_simple_graph_100,
    bench_seidel_simple_graph_1000,
    bench_petgraph_fw_simple_graph_1000,
    bench_fw_simple_graph_1000,
);
