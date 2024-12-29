use std::collections::HashSet;
use std::hash::Hash;

use crate::traits::EdgeCount;
use petgraph::visit::{EdgeRef, IntoEdgeReferences, IntoNodeIdentifiers, NodeCount, NodeIndexable};

/// Graph`s complement.
///
/// Returns the complement of the input directed graph as a set of edges in the format `(usize, usize)`,
/// where each number is the index of the corresponding vertex.
///
/// # Examples
///
/// ```
/// use petgraph::Graph;
/// use graphalgs::generate::complement;
/// use std::collections::HashSet;
///
/// // Create the following graph:
/// //  0 -- 1
/// //  |    |
/// //  3 -- 2
///
/// let graph = Graph::<(), ()>::from_edges(&[
///     (0, 1, ()), (1, 2, ()), (2, 3, ()), (3, 0, ()),
///     (1, 0, ()), (2, 1, ()), (3, 2, ()), (0, 3, ()),
/// ]);
///
/// // It's complement consists of two pairs of vertices:
/// // 0 -- 2
/// // 1 -- 3
///
/// let mut compl = HashSet::<(usize, usize)>::new();
/// compl.insert((0, 2)); compl.insert((2, 0));
/// compl.insert((1, 3)); compl.insert((3, 1));
///
/// assert_eq!(complement(&graph), compl);
/// ```
pub fn complement<G>(graph: G) -> HashSet<(usize, usize)>
where
    G: IntoEdgeReferences + NodeCount + EdgeCount + IntoNodeIdentifiers + NodeIndexable,
    G::NodeId: Eq + Hash,
{
    let mut edges: HashSet<(G::NodeId, G::NodeId)> =
        HashSet::with_capacity(graph.number_of_edges());

    for edge in graph.edge_references() {
        edges.insert((edge.source(), edge.target()));
    }

    let n = graph.node_count();
    let edge_count = n * (n - 1) - graph.number_of_edges();
    let mut compl: HashSet<(usize, usize)> = HashSet::with_capacity(edge_count);

    for i in graph.node_identifiers() {
        for j in graph.node_identifiers() {
            if i != j && !edges.contains(&(i, j)) {
                compl.insert((graph.to_index(i), graph.to_index(j)));
            }
        }
    }

    compl
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::random_digraph;
    use petgraph::algo::is_isomorphic;
    use petgraph::graph::Graph;
    use petgraph::Directed;

    #[test]
    fn test_complement() {
        let mut graph = Graph::<(), ()>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());
        let n3 = graph.add_node(());

        graph.add_edge(n0, n1, ());
        graph.add_edge(n1, n0, ());
        graph.add_edge(n1, n2, ());
        graph.add_edge(n2, n1, ());
        graph.add_edge(n1, n3, ());
        graph.add_edge(n3, n1, ());

        let expected = vec![(0, 2), (2, 0), (0, 3), (3, 0), (2, 3), (3, 2)]
            .into_iter()
            .collect::<HashSet<(usize, usize)>>();

        assert_eq!(complement(&graph), expected);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_complement_random() {
        for _ in 0..10 {
            let graph =
                Graph::<(), (), Directed, usize>::from_edges(random_digraph(20, 150).unwrap());
            let compl = Graph::<(), (), Directed, usize>::from_edges(complement(&graph));
            let compl_compl = Graph::<(), (), Directed, usize>::from_edges(complement(&compl));
            assert!(is_isomorphic(&graph, &compl_compl));
        }
    }
}
