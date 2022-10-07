pub use petgraph::algo::FloatMeasure;
use petgraph::visit::{
    EdgeRef, IntoEdgeReferences, IntoEdges, IntoNodeIdentifiers, NodeCount, NodeIndexable,
};

/// [Prim's algorithm](https://en.wikipedia.org/wiki/Prim%27s_algorithm)
/// for computing a minimum spanning tree of a graph.
///
/// The input graph is treated as if undirected.
/// Using improved Prim's algorithm with runtime O(|V|^2). The function actually returns a minimum spanning forest,
/// i.e. a minimum spanning tree for each connected component of the graph.
///
/// ## Arguments
/// * `graph`: weighted undirected graph.
/// * `edge_cost`: closure that returns cost of a particular edge.
///
/// ## Returns
/// * `Vec<(usize, usize)>`: the vector of edges of the resulting MST,
///     where each edge is denoted by a pair of vertex indices, index order is random.
///
/// # Examples
/// ```
/// use graphalgs::mst::prim;
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
///     prim(&graph, |edge| *edge.weight()),
///     vec![(2, 0), (3, 2), (1, 3), (5, 2), (4, 5)]
/// );
/// ```
pub fn prim<G, F, K>(graph: G, mut edge_cost: F) -> Vec<(usize, usize)>
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount + IntoEdges,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure,
{
    let mut msf: Vec<(usize, usize)> = Vec::new();
    let mut used = vec![false; graph.node_count()];
    let mut used_count = 0usize;
    let mut sel_e = vec![graph.node_count(); graph.node_count()];
    let mut min_e = vec![K::infinite(); graph.node_count()];

    while used_count < graph.node_count() {
        let mut next_node = graph.node_count();
        for n in 0..graph.node_count() {
            if !used[n] && (next_node == graph.node_count() || min_e[n] < min_e[next_node]) {
                next_node = n;
            }
        }

        if min_e[next_node] == K::infinite() {
            min_e[next_node] = K::zero();
            continue; // next_node belongs to the new connected component
        }

        used[next_node] = true;
        used_count += 1;

        if sel_e[next_node] != graph.node_bound() {
            let pred = sel_e[next_node];
            msf.push((next_node, pred));
        }

        for edge in graph.edges(graph.from_index(next_node)) {
            let to = graph.to_index(edge.target());
            if edge_cost(edge) < min_e[to] {
                min_e[to] = edge_cost(edge);
                sel_e[to] = next_node;
            }
        }
    }

    msf
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::{Graph, UnGraph};

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
    fn test_prim() {
        assert_eq!(
            prim(&graph1(), |edge| *edge.weight()),
            vec![(4, 0), (1, 4), (3, 1), (2, 3)]
        );
        assert_eq!(
            prim(&graph2(), |edge| *edge.weight()),
            vec![(1, 0), (2, 1), (4, 3), (5, 4), (6, 5)]
        );
        assert_eq!(
            prim(&graph1(), |edge| -*edge.weight()),
            vec![(1, 0), (2, 1), (4, 0), (3, 4)]
        );
        assert_eq!(
            prim(&graph2(), |edge| -*edge.weight()),
            vec![(2, 0), (1, 2), (4, 3), (6, 4), (5, 4)]
        );
    }
}
