//use std::collections::VecDeque;
use crate::shortest_path::floyd_warshall::NegativeCycle;
use petgraph::algo::FloatMeasure;
use petgraph::visit::{EdgeRef, IntoEdges, IntoNodeIdentifiers, NodeIndexable};

/// [Shortest Path Faster Algorithm](https://en.wikipedia.org/wiki/Shortest_Path_Faster_Algorithm).
/// Compute shortest distances from node `source` to all other.
///
/// Compute shortest paths lengths in a weighted graph with positive or negative edge weights,
/// but with no negative cycles.
///
/// ## Arguments
/// * `graph`: weighted graph.
/// * `source`: the source vertex, for which we calculate the lengths of the shortest paths to all the others.
///
/// ## Returns
/// * `Err`: if graph contains negative cycle.
/// * `Ok`: a pair of a vector of shortest distances and a vector
///         of predecessors of each vertex along the shortest path.
///
/// # Examples
///
/// ```
/// use petgraph::Graph;
/// use graphalgs::shortest_path::spfa;
///
/// let mut g = Graph::new();
/// let a = g.add_node(()); // node with no weight
/// let b = g.add_node(());
/// let c = g.add_node(());
/// let d = g.add_node(());
/// let e = g.add_node(());
/// let f = g.add_node(());
/// g.extend_with_edges(&[
///     (0, 1, 3.0),
///     (0, 3, 2.0),
///     (1, 2, 1.0),
///     (1, 5, 7.0),
///     (2, 4, -4.0),
///     (3, 4, -1.0),
///     (4, 5, 1.0),
/// ]);
///
/// // Graph represented with the weight of each edge.
/// //
/// //     3       1
/// // a ----- b ----- c
/// // | 2     | 7     |
/// // d       f       | -4
/// // | -1    | 1     |
/// // \------ e ------/
///
/// assert_eq!(spfa(&g, a), Ok((vec![0.0 ,     3.0,     4.0,    2.0,     0.0,     1.0],
///                             vec![None, Some(a), Some(b), Some(a), Some(c), Some(e)]
///                           ))
///           );
///
///
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)]);
///
/// assert!(spfa(&graph, 0.into()).is_err());
/// ```
#[allow(clippy::type_complexity)]
pub fn spfa<G>(
    graph: G,
    source: G::NodeId,
) -> Result<(Vec<G::EdgeWeight>, Vec<Option<G::NodeId>>), NegativeCycle>
where
    G: IntoEdges + IntoNodeIdentifiers + NodeIndexable,
    G::EdgeWeight: FloatMeasure,
{
    let ix = |i| graph.to_index(i);

    let mut predecessor = vec![None; graph.node_bound()];
    let mut distance = vec![<_>::infinite(); graph.node_bound()];
    distance[ix(source)] = <_>::zero();

    // Queue of vertices capable of relaxation of the found shortest distances.
    let mut queue: Vec<G::NodeId> = Vec::with_capacity(graph.node_bound());
    let mut in_queue = vec![false; graph.node_bound()];
    queue.push(source);
    in_queue[ix(source)] = true;

    // We will keep track of how many times each vertex appeared
    // in the queue to be able to detect a negative cycle.
    let mut visits = vec![0; graph.node_bound()];

    while let Some(i) = queue.pop() {
        in_queue[ix(i)] = false;

        // In a graph without a negative cycle, no vertex can improve
        // the shortest distances by more than |V| times.
        if visits[ix(i)] >= graph.node_bound() {
            return Err(NegativeCycle {});
        }
        visits[ix(i)] += 1;

        for edge in graph.edges(i) {
            let j = edge.target();
            let w = *edge.weight();

            if distance[ix(i)] + w < distance[ix(j)] {
                distance[ix(j)] = distance[ix(i)] + w;
                predecessor[ix(j)] = Some(i);

                if !in_queue[ix(j)] {
                    in_queue[ix(j)] = true;
                    queue.push(j);
                }
            }
        }
    }

    Ok((distance, predecessor))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::random_weighted_digraph;
    use crate::shortest_path::bellman_ford;
    use petgraph::graph::Graph;
    use petgraph::Directed;
    use rand::Rng;

    fn graph1() -> Graph<(), f64> {
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

    fn graph2() -> Graph<(), f32> {
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
    fn test_spfa() {
        let inf = f32::INFINITY;

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

        assert_eq!(
            spfa(&graph, 0.into()).unwrap().0,
            vec![0.0, 1.0, -4.0, 16.0, 6.0, inf]
        );
        assert_eq!(
            spfa(&graph, 1.into()).unwrap().0,
            vec![inf, 0.0, -5.0, 15.0, 5.0, inf]
        );
        assert_eq!(
            spfa(&graph, 2.into()).unwrap().0,
            vec![inf, 8.0, 0.0, 23.0, 13.0, inf]
        );
        assert_eq!(
            spfa(&graph, 3.into()).unwrap().0,
            vec![inf, -12.0, -20.0, 0.0, -7.0, inf]
        );
        assert_eq!(
            spfa(&graph, 4.into()).unwrap().0,
            vec![inf, -2.0, -10.0, 10.0, 0.0, inf]
        );
        assert_eq!(
            spfa(&graph, 5.into()).unwrap().0,
            vec![inf, -4.0, -9.0, 11.0, 1.0, 0.0]
        );
    }

    #[test]
    fn test_spfa_strongly_connected() {
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

        assert_eq!(
            spfa(&graph, 0.into()).unwrap().0,
            vec![0.0, 33.0, 52.0, 38.0, 18.0]
        );
        assert_eq!(
            spfa(&graph, 1.into()).unwrap().0,
            vec![33.0, 0.0, 20.0, 6.0, 15.0]
        );
        assert_eq!(
            spfa(&graph, 2.into()).unwrap().0,
            vec![52.0, 20.0, 0.0, 14.0, 34.0]
        );
        assert_eq!(
            spfa(&graph, 3.into()).unwrap().0,
            vec![38.0, 6.0, 14.0, 0.0, 20.0]
        );
        assert_eq!(
            spfa(&graph, 4.into()).unwrap().0,
            vec![18.0, 15.0, 34.0, 20.0, 0.0]
        );
    }

    #[test]
    fn test_spfa_single_node() {
        let mut graph = Graph::<(), f32>::new();
        graph.add_node(());
        assert_eq!(spfa(&graph, 0.into()).unwrap().0, vec![0.0]);
    }

    #[test]
    fn test_spfa_negative_cycle() {
        assert!(spfa(&graph1(), 0.into()).is_err());
        assert!(spfa(&graph2(), 0.into()).is_err());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_spfa_random() {
        // Random tests against bellman_ford
        let mut rng = rand::thread_rng();

        for n in 2..=50 {
            let graph = Graph::<(), f64, Directed, usize>::from_edges(
                random_weighted_digraph(n, rng.gen_range(1..n * (n - 1)), -10f64, 1000f64)
                    .unwrap()
                    .into_iter()
                    .map(|(edge, w)| (edge.0, edge.1, w.round())),
            );

            for v in 0..graph.node_count() {
                let spfa_res = spfa(&graph, v.into());
                let bf_res = bellman_ford(&graph, v.into());

                if let Ok((spfa_dist, spfa_pred)) = spfa_res {
                    let bf_res = bf_res.unwrap();
                    let bf_dist = bf_res.distances;
                    let bf_pred = bf_res.predecessors;
                    assert_eq!(spfa_dist, bf_dist);

                    // Several shortest paths can exist to vertex.
                    for i in 0..graph.node_count() {
                        let s = spfa_pred[i];
                        let b = bf_pred[i];
                        match s {
                            None => assert!(b.is_none()),
                            Some(pred) => assert_eq!(
                                spfa_dist[graph.to_index(pred)]
                                    + graph[graph.find_edge(pred, i.into()).unwrap()],
                                bf_dist[graph.to_index(pred)]
                                    + graph[graph.find_edge(pred, i.into()).unwrap()],
                            ),
                        }
                    }
                } else {
                    assert!(bf_res.is_err());
                }
            }
        }
    }
}
