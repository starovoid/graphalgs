use crate::spec::laplacian_matrix;
use petgraph::visit::{GraphProp, IntoEdges, IntoNodeIdentifiers, NodeCount, NodeIndexable};

/// Count spanning trees oriented to `root`.
///
/// For an undirected graph, the choice of the `root` vertex does not affect the answer.
///
/// # Examples
/// ```no_run
/// use graphalgs::spec::count_spanning_trees;
/// use petgraph::graph::{Graph, UnGraph};
///
/// // Let 's construct the following undirected graph:
/// // 3 --- 0
/// // | ___/|
/// // |/    |
/// // 2 --- 1
///
/// // It contains 8 spanning trees:
/// // 3 --- 0      3 --- 0      3 --- 0      3     0
/// //       |      |            |     |      |     |
/// //       |      |            |     |      |     |
/// // 2 --- 1      2 --- 1      2     1      2 --- 1
///
/// // 3 --- 0      3 --- 0      3     0      3     0
/// //   ___/         ___/|      | ___/       | ___/|
/// //  /            /    |      |/           |/    |  
/// // 2 --- 1      2     1      2 --- 1      2     1
///
/// let mut ungraph = UnGraph::<u32, ()>::new_undirected();
///
/// let n0 = ungraph.add_node(0);
/// let n1 = ungraph.add_node(1);
/// let n2 = ungraph.add_node(2);
/// let n3 = ungraph.add_node(3);
///
/// ungraph.add_edge(n0, n1, ());
/// ungraph.add_edge(n1, n2, ());
/// ungraph.add_edge(n0, n3, ());
/// ungraph.add_edge(n0, n2, ());
/// ungraph.add_edge(n3, n2, ());
///
/// assert_eq!(count_spanning_trees(&ungraph, n0), 8);
/// assert_eq!(count_spanning_trees(&ungraph, n1), 8);
/// assert_eq!(count_spanning_trees(&ungraph, n2), 8);
/// assert_eq!(count_spanning_trees(&ungraph, n3), 8);
///
///
///
/// // Now make our graph oriented:
/// // 3 --> 0
/// // ^ _>_/|
/// // |/    v
/// // 2 --> 1
///
/// // It contains three spanning trees oriented to node 1 and zero oriented to other:
/// // 3 --> 0      3 --> 0      3 --> 0
/// //       |        _>_/|      ^     |
/// //       v       /    v      |     v
/// // 2 --> 1      3     2      2     1
///
/// let mut digraph = Graph::<u32, f32>::new();
/// let n0 = digraph.add_node(0);
/// let n1 = digraph.add_node(1);
/// let n2 = digraph.add_node(2);
/// let n3 = digraph.add_node(3);
///
/// digraph.add_edge(n0, n1, 10.0);
/// digraph.add_edge(n2, n1, 20.0);
/// digraph.add_edge(n3, n0, 30.0);
/// digraph.add_edge(n2, n0, 40.0);
/// digraph.add_edge(n2, n3, 50.0);
///
/// assert_eq!(count_spanning_trees(&digraph, n0), 0);
/// assert_eq!(count_spanning_trees(&digraph, n1), 3);
/// assert_eq!(count_spanning_trees(&digraph, n2), 0);
/// assert_eq!(count_spanning_trees(&digraph, n3), 0);
/// ```
pub fn count_spanning_trees<G>(graph: G, root: G::NodeId) -> usize
where
    G: IntoEdges + IntoNodeIdentifiers + NodeCount + NodeIndexable + GraphProp,
{
    let mut mtrx = laplacian_matrix(graph, |_| 1.0f32);
    mtrx = mtrx.remove_row(graph.to_index(root));
    mtrx = mtrx.remove_column(graph.to_index(root));
    mtrx.determinant() as usize
}

#[cfg(test)]
mod test {
    use super::*;
    use petgraph::graph::{Graph, UnGraph};

    #[test]
    #[cfg_attr(miri, ignore)]
    // Ignore it because MIRI finds an error in the safe nalgebra API. This requires separate clarifications.
    fn test_count_spanning_trees() {
        let mut graph = UnGraph::<u32, f32>::new_undirected();
        let n0 = graph.add_node(0);
        assert_eq!(count_spanning_trees(&graph, n0), 1);
        let n1 = graph.add_node(1);
        assert_eq!(count_spanning_trees(&graph, n0), 0);
        assert_eq!(count_spanning_trees(&graph, n0), 0);

        let n2 = graph.add_node(2);
        let n3 = graph.add_node(3);

        graph.add_edge(n0, n1, 10.0);
        graph.add_edge(n1, n2, 20.0);
        graph.add_edge(n0, n3, 30.0);
        graph.add_edge(n0, n2, 40.0);
        graph.add_edge(n3, n2, 50.0);

        assert_eq!(count_spanning_trees(&graph, n0), 8);
        assert_eq!(count_spanning_trees(&graph, n1), 8);
        assert_eq!(count_spanning_trees(&graph, n2), 8);
        assert_eq!(count_spanning_trees(&graph, n3), 8);

        graph.add_edge(n1, n0, 10.0);
        assert_eq!(count_spanning_trees(&graph, n0), 13);
        assert_eq!(count_spanning_trees(&graph, n1), 13);
        assert_eq!(count_spanning_trees(&graph, n2), 13);
        assert_eq!(count_spanning_trees(&graph, n3), 13);

        let mut digraph = Graph::<u32, f32>::new();
        let n0 = digraph.add_node(0);
        assert_eq!(count_spanning_trees(&digraph, n0), 1);
        let n1 = digraph.add_node(1);
        assert_eq!(count_spanning_trees(&digraph, n0), 0);
        assert_eq!(count_spanning_trees(&digraph, n0), 0);

        let n2 = digraph.add_node(2);
        let n3 = digraph.add_node(3);

        digraph.add_edge(n0, n1, 10.0);
        digraph.add_edge(n2, n1, 20.0);
        digraph.add_edge(n3, n0, 30.0);
        digraph.add_edge(n2, n0, 40.0);
        digraph.add_edge(n2, n3, 50.0);

        assert_eq!(count_spanning_trees(&digraph, n0), 0);
        assert_eq!(count_spanning_trees(&digraph, n1), 3);
        assert_eq!(count_spanning_trees(&digraph, n2), 0);
        assert_eq!(count_spanning_trees(&digraph, n3), 0);

        digraph.add_edge(n1, n0, 10.0);
        assert_eq!(count_spanning_trees(&digraph, n0), 3);
        assert_eq!(count_spanning_trees(&digraph, n1), 3);
        assert_eq!(count_spanning_trees(&digraph, n2), 0);
        assert_eq!(count_spanning_trees(&digraph, n3), 0);
    }
}
