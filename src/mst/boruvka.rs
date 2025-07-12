pub use petgraph::algo::FloatMeasure;
use petgraph::unionfind::UnionFind;
use petgraph::visit::{
    EdgeRef, IntoEdgeReferences, IntoEdges, IntoNodeIdentifiers, NodeCount, NodeIndexable,
};
use std::collections::HashSet;

/// [Borůvka's algorithm](https://en.wikipedia.org/wiki/Bor%C5%AFvka%27s_algorithm)
/// for computing a minimum spanning tree of a graph.
///
/// The input graph is treated as if undirected.
/// Uses the Boruvka's algorithm with the UnionFind structure.
/// The function actually returns a minimum spanning forest,
/// i.e. a minimum spanning tree for each connected component of the graph.
///
/// ## Arguments
/// * `graph`: weighted undirected graph.
/// * `edge_cost`: closure that returns cost of a particular edge.
///
/// ## Returns
/// * `HashSet<(usize, usize)>`: the set of edges of the resulting MST,
///   where each edge is denoted by a pair of vertex indices, index order is random.
///
/// # Examples
/// ```
/// use std::collections::HashSet;
/// use graphalgs::mst::boruvka;
/// use petgraph::graph::UnGraph;
///
/// let mut graph: UnGraph<(), f64> = UnGraph::new_undirected();
/// let n0 = graph.add_node(()); let n1 = graph.add_node(());
/// let n2 = graph.add_node(()); let n3 = graph.add_node(());
/// let n4 = graph.add_node(()); let n5 = graph.add_node(());
///
/// graph.add_edge(n0, n1, 10.0); graph.add_edge(n1, n3, 4.0);
/// graph.add_edge(n2, n3, -5.0); graph.add_edge(n2, n0, -2.0);
/// graph.add_edge(n2, n5, 6.0); graph.add_edge(n5, n4, 2.0);
/// graph.add_edge(n3, n4, 10.0);
///
/// assert_eq!(
///     boruvka(&graph, |edge| *edge.weight()),
///     vec![(5, 4), (1, 3), (2, 0), (2, 3), (2, 5)].into_iter()
///         .collect::<HashSet<(usize, usize)>>()
/// );
/// ```
pub fn boruvka<G, F, K>(graph: G, mut edge_cost: F) -> HashSet<(usize, usize)>
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount + IntoEdges,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure,
{
    let mut msf: HashSet<(usize, usize)> = HashSet::new();
    let mut components = UnionFind::<usize>::new(graph.node_count());

    loop {
        let mut min_edge_cost: Vec<K> = vec![K::infinite(); graph.node_count()];
        let mut min_edge: Vec<Option<(usize, usize)>> = vec![None; graph.node_count()];

        for edge in graph.edge_references() {
            let s = graph.to_index(edge.source());
            let t = graph.to_index(edge.target());
            let s_comp = components.find(s);
            let t_comp = components.find(t);
            let c = edge_cost(edge);

            if s_comp != t_comp {
                if c < min_edge_cost[s_comp] {
                    min_edge[s_comp] = Some((s, t));
                    min_edge_cost[s_comp] = c;
                }
                if c < min_edge_cost[t_comp] {
                    min_edge[t_comp] = Some((s, t));
                    min_edge_cost[t_comp] = c;
                }
            }
        }

        let mut union_occurred = false;
        for k in 0..graph.node_count() {
            if let Some((s, t)) = min_edge[components.find(k)] {
                if components.union(s, t) {
                    union_occurred = true;
                }
                msf.insert((s, t));
            }
        }

        if !union_occurred {
            break;
        }
    }

    msf
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::random_weighted_ungraph;
    use crate::mst::prim;
    use petgraph::graph::{Graph, UnGraph};
    use std::collections::HashSet;

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

    fn graph2() -> UnGraph<i8, f64> {
        let mut graph = UnGraph::<i8, f64>::new_undirected();
        let n0 = graph.add_node(0);
        let n1 = graph.add_node(1);
        let n2 = graph.add_node(2);
        let n3 = graph.add_node(3);
        let n4 = graph.add_node(4);
        let n5 = graph.add_node(5);
        let n6 = graph.add_node(6);

        graph.add_edge(n0, n2, 5.0);
        graph.add_edge(n1, n0, 1.0);
        graph.add_edge(n1, n2, 2.0);
        graph.add_edge(n3, n4, 2.0);
        graph.add_edge(n5, n4, 3.0);
        graph.add_edge(n4, n6, 6.0);
        graph.add_edge(n6, n5, 3.0);

        graph
    }

    #[test]
    fn test_boruvka() {
        assert_eq!(
            boruvka(&graph1(), |edge| *edge.weight()),
            vec![(0, 4), (1, 4), (1, 3), (2, 3)]
                .into_iter()
                .collect::<HashSet<(usize, usize)>>()
        );
        assert_eq!(
            boruvka(&graph2(), |edge| *edge.weight()),
            vec![(1, 0), (1, 2), (3, 4), (5, 4), (6, 5)]
                .into_iter()
                .collect::<HashSet<(usize, usize)>>()
        );
        assert_eq!(
            boruvka(&graph1(), |edge| -*edge.weight()),
            vec![(0, 1), (1, 2), (0, 4), (3, 4)]
                .into_iter()
                .collect::<HashSet<(usize, usize)>>()
        );
        assert_eq!(
            boruvka(&graph2(), |edge| -*edge.weight()),
            vec![(0, 2), (1, 2), (3, 4), (4, 6), (5, 4)]
                .into_iter()
                .collect::<HashSet<(usize, usize)>>()
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_boruvka_with_prim_random_50_1000() {
        for _ in 0..20 {
            let graph: UnGraph<(), f64, usize> = UnGraph::from_edges(
                random_weighted_ungraph(50, 1000, -100.0, 100.0)
                    .unwrap()
                    .into_iter()
                    .map(|(edge, w)| (edge.0, edge.1, w)),
            );

            let boruvka_output = boruvka(&graph, |edge| *edge.weight());
            let prim_output = prim(&graph, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<(usize, usize)>>();

            compare(boruvka_output, prim_output);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_boruvka_with_prim_random_500_250() {
        for _ in 0..20 {
            let graph: UnGraph<(), f64, usize> = UnGraph::from_edges(
                random_weighted_ungraph(500, 250, -100.0, 100.0)
                    .unwrap()
                    .into_iter()
                    .map(|(edge, w)| (edge.0, edge.1, w)),
            );

            let boruvka_output = boruvka(&graph, |edge| *edge.weight());
            let prim_output = prim(&graph, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<(usize, usize)>>();

            compare(boruvka_output, prim_output);
        }
    }
    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_boruvka_with_prim_random_10_30() {
        for _ in 0..100 {
            let graph: UnGraph<(), f64, usize> = UnGraph::from_edges(
                random_weighted_ungraph(10, 30, -100.0, 100.0)
                    .unwrap()
                    .into_iter()
                    .map(|(edge, w)| (edge.0, edge.1, w)),
            );

            let boruvka_output = boruvka(&graph, |edge| *edge.weight());
            let prim_output = prim(&graph, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<(usize, usize)>>();

            compare(boruvka_output, prim_output);
        }
    }

    fn compare(
        mut boruvka_edges: HashSet<(usize, usize)>,
        mut prim_edges: HashSet<(usize, usize)>,
    ) {
        let temp: HashSet<(usize, usize)> = boruvka_edges.iter().map(|&(a, b)| (b, a)).collect();
        boruvka_edges.extend(temp);

        let temp: HashSet<(usize, usize)> = prim_edges.iter().map(|&(a, b)| (b, a)).collect();
        prim_edges.extend(temp);

        assert_eq!(boruvka_edges, prim_edges);
    }
}
