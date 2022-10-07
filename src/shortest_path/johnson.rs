use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};
use std::ops::Sub;

use crate::shortest_path::NegativeCycle;
pub use petgraph::algo::FloatMeasure;
use petgraph::visit::{
    EdgeRef, IntoEdges, IntoNodeIdentifiers, NodeIndexable, VisitMap, Visitable,
};

/// [Johnson algorithm](https://en.wikipedia.org/wiki/Johnson%27s_algorithm) for all pairs shortest path problem.
///
/// Сompute the lengths of shortest paths in a weighted graph with
/// positive or negative edge weights, but no negative cycles.
///
/// ## Arguments
/// * `graph`: weighted graph.
/// * `edge_cost`: closure that returns cost of a particular edge.
///
/// ## Returns
/// * `Err`: if graph contains negative cycle.
/// * `Ok`: matrix `Vec<Vec<K>>` of shortest distances, in cell **(i, j)** of which the length of the shortest path
///         from node **i** to node **j** is stored.
///
/// # Examples
///
/// ```
/// use graphalgs::shortest_path::johnson;
/// use petgraph::Graph;
///
/// let inf = f32::INFINITY;
///
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0),
///     (3, 2, 2.0), (2, 3, 20.0),
/// ]);
///
/// // Graph represented with the weight of each edge.
/// //        2
/// //  (0)------->(1)
/// //    ___10____/|
/// //   /          | -5
/// //   v          v
/// //  (2)<--2----(3)
/// //   \----20--->/
///
/// assert_eq!(
///     johnson(&graph, |edge| *edge.weight()),
///     Ok(vec![vec![0.0, 2.0, -1.0, -3.0],
///             vec![inf, 0.0, -3.0, -5.0],
///             vec![inf, inf,  0.0, 20.0],
///             vec![inf, inf,  2.0,  0.0]])
/// );
///
///
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)]);
///
/// assert!(johnson(&graph, |edge| *edge.weight()).is_err());
/// ```
pub fn johnson<G, F, K>(graph: G, mut edge_cost: F) -> Result<Vec<Vec<K>>, NegativeCycle>
where
    G: IntoEdges + IntoNodeIdentifiers + NodeIndexable + Visitable,
    G::NodeId: Eq,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure + Sub<K, Output = K>,
{
    // Add a new vertex to the graph with oriented edges with zero weight
    // to all other vertices, and then run SPFA from it.
    // The found distances will be used to change the edge weights in Dijkstra's
    // algorithm to make them non-negative.

    let ix = |i| graph.to_index(i);

    let mut h = vec![K::zero(); graph.node_bound()];

    // Queue of vertices capable of relaxation of the found shortest distances.
    let mut queue: VecDeque<G::NodeId> = VecDeque::with_capacity(graph.node_bound());
    queue.extend(graph.node_identifiers());
    let mut in_queue = vec![true; graph.node_bound()];

    // We will keep track of how many times each vertex appeared
    // in the queue to be able to detect a negative cycle.
    let mut visits = vec![0; graph.node_bound()];

    while !queue.is_empty() {
        let i = queue.pop_front().unwrap();
        in_queue[ix(i)] = false;

        // In a graph without a negative cycle, no vertex can improve
        // the shortest distances by more than |V| times.
        if visits[ix(i)] >= graph.node_bound() {
            return Err(NegativeCycle {});
        }
        visits[ix(i)] += 1;

        for edge in graph.edges(i) {
            let j = edge.target();
            let w = edge_cost(edge);

            if h[ix(i)] + w < h[ix(j)] {
                h[ix(j)] = h[ix(i)] + w;

                if !in_queue[ix(j)] {
                    in_queue[ix(j)] = true;
                    queue.push_back(j);
                }
            }
        }
    }

    // Run Dijkstra's algorithm from each vertex.
    Ok(graph
        .node_identifiers()
        .map(|n| dijkstra_helper(&graph, n, &h, &mut edge_cost))
        .enumerate()
        .map(|(source, dist)| {
            dist.into_iter()
                .enumerate()
                .map(|(target, d)| d + h[target] - h[source])
                .collect()
        })
        .collect())
}

/// Dijkstra's algorithm calculating shortest distances taking into account changes in weights.
/// Vector h - potential function calculated for each vertex.
/// The weight of each edge is recalculated using the formula
/// new_weight = weight(a, b) = h(a) - h(b).
fn dijkstra_helper<G, F, K>(graph: G, start: G::NodeId, h: &Vec<K>, edge_cost: &mut F) -> Vec<K>
where
    G: IntoEdges + Visitable + NodeIndexable,
    G::NodeId: Eq,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure + Sub<K, Output = K>,
{
    let ix = |i| graph.to_index(i);
    let mut visited = graph.visit_map();
    let mut distance = vec![K::infinite(); graph.node_bound()];
    let mut visit_next = BinaryHeap::new();

    distance[ix(start)] = K::zero();
    visit_next.push(MinScored(K::zero(), start));

    while let Some(MinScored(node_score, node)) = visit_next.pop() {
        if visited.is_visited(&node) {
            continue;
        }
        for edge in graph.edges(node) {
            let next = edge.target();
            if visited.is_visited(&next) {
                continue;
            }
            let next_score = node_score + edge_cost(edge) + h[ix(node)] - h[ix(next)];
            if next_score < distance[ix(next)] {
                distance[ix(next)] = next_score;
            }
            visit_next.push(MinScored(next_score, next));
        }
        visited.visit(node);
    }

    distance
}

/// A pair for use with a `BinaryHeap` in `dijkstra_helper`.
#[derive(Copy, Clone, Debug)]
pub struct MinScored<K, T>(pub K, pub T);

impl<K: PartialOrd, T> PartialEq for MinScored<K, T> {
    #[inline]
    fn eq(&self, other: &MinScored<K, T>) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<K: PartialOrd, T> Eq for MinScored<K, T> {}

impl<K: PartialOrd, T> PartialOrd for MinScored<K, T> {
    #[inline]
    fn partial_cmp(&self, other: &MinScored<K, T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: PartialOrd, T> Ord for MinScored<K, T> {
    #[inline]
    fn cmp(&self, other: &MinScored<K, T>) -> Ordering {
        let a = &self.0;
        let b = &other.0;
        if a > b {
            Ordering::Less
        } else if a < b {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::random_weighted_digraph;
    use crate::shortest_path::floyd_warshall;
    use petgraph::graph::Graph;
    use petgraph::Directed;
    use rand::Rng;

    fn graph1() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());
        let n3 = graph.add_node(());
        let n4 = graph.add_node(());

        graph.add_edge(n0, n1, 40.0);
        graph.add_edge(n0, n4, 18.0);
        graph.add_edge(n1, n0, 40.0);
        graph.add_edge(n1, n4, 15.0);
        graph.add_edge(n1, n2, 22.0);
        graph.add_edge(n1, n3, 6.0);
        graph.add_edge(n2, n1, 22.0);
        graph.add_edge(n2, n3, 14.0);
        graph.add_edge(n3, n4, 20.0);
        graph.add_edge(n3, n1, 6.0);
        graph.add_edge(n3, n2, 14.0);
        graph.add_edge(n4, n0, 18.0);
        graph.add_edge(n4, n1, 15.0);
        graph.add_edge(n4, n3, 20.0);

        graph
    }

    fn graph2() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());
        let n3 = graph.add_node(());
        let n4 = graph.add_node(());
        let n5 = graph.add_node(());

        graph.add_edge(n0, n1, 1.0);
        graph.add_edge(n5, n1, -4.0);
        graph.add_edge(n1, n4, 5.0);
        graph.add_edge(n4, n1, 5.0);
        graph.add_edge(n2, n1, 8.0);
        graph.add_edge(n4, n3, 10.0);
        graph.add_edge(n3, n2, 0.0);
        graph.add_edge(n3, n2, -20.0);

        graph
    }

    fn graph3() -> Graph<(), f64> {
        let mut graph = Graph::<(), f64>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());
        let n3 = graph.add_node(());

        graph.add_edge(n0, n1, 10.0);
        graph.add_edge(n0, n2, 5.0);
        graph.add_edge(n1, n2, 2.0);
        graph.add_edge(n2, n3, -10.0);
        graph.add_edge(n3, n1, -1.0);
        graph.add_edge(n1, n3, 16.0);

        graph
    }

    fn graph4() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        graph.add_node(());
        graph
    }

    fn graph5() -> Graph<(), f32> {
        Graph::<(), f32>::new()
    }

    fn graph6() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());

        graph.add_edge(n0, n1, 1.0);
        graph.add_edge(n1, n0, -10.0);
        graph.add_edge(n2, n2, 5.0);
        graph
    }

    #[test]
    fn test_johnson() {
        let inf = f32::INFINITY;

        assert_eq!(
            johnson(&graph1(), |edge| *edge.weight()),
            Ok(vec![
                vec![0.0, 33.0, 52.0, 38.0, 18.0],
                vec![33.0, 0.0, 20.0, 6.0, 15.0],
                vec![52.0, 20.0, 0.0, 14.0, 34.0],
                vec![38.0, 6.0, 14.0, 0.0, 20.0],
                vec![18.0, 15.0, 34.0, 20.0, 0.0]
            ])
        );

        assert_eq!(
            johnson(&graph2(), |edge| *edge.weight()),
            Ok(vec![
                vec![0.0, 1.0, -4.0, 16.0, 6.0, inf],
                vec![inf, 0.0, -5.0, 15.0, 5.0, inf],
                vec![inf, 8.0, 0.0, 23.0, 13.0, inf],
                vec![inf, -12.0, -20.0, 0.0, -7.0, inf],
                vec![inf, -2.0, -10.0, 10.0, 0.0, inf],
                vec![inf, -4.0, -9.0, 11.0, 1.0, 0.0],
            ])
        );

        // Graphs with negative cycle
        assert_eq!(
            johnson(&graph3(), |edge| *edge.weight()),
            Err(NegativeCycle {})
        );
        assert_eq!(
            johnson(&graph6(), |edge| *edge.weight()),
            Err(NegativeCycle {})
        );

        let mut graph = graph1();
        graph.add_edge(3.into(), 3.into(), -5.0);
        assert_eq!(
            johnson(&graph, |edge| *edge.weight()),
            Err(NegativeCycle {})
        );

        // Edge cases
        assert_eq!(
            johnson(&graph4(), |edge| *edge.weight()),
            Ok(vec![vec![0.0]])
        );
        assert_eq!(johnson(&graph5(), |edge| *edge.weight()), Ok(vec![]));

        // Random tests

        let mut rng = rand::thread_rng();

        for n in 2..=50 {
            let graph = Graph::<(), f64, Directed, usize>::from_edges(
                random_weighted_digraph(n, rng.gen_range(1..n * (n - 1)), -10f64, 1000f64)
                    .unwrap()
                    .into_iter()
                    .map(|(edge, w)| (edge.0, edge.1, w.round())),
            );

            assert_eq!(
                johnson(&graph, |edge| *edge.weight()),
                floyd_warshall(&graph, |edge| *edge.weight())
            );
        }
    }
}
