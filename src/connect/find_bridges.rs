use petgraph::visit::{IntoNeighbors, IntoNodeIdentifiers, NodeIndexable};

/// Find all [bridges](https://en.wikipedia.org/wiki/Bridge_(graph_theory)) in a simple undirected graph.
///
/// Returns the vector of pairs `(G::NodeID, G:: NodeID)`,
/// representing the edges of the input graph that are bridges.
/// The order of the vertices in the pair and the order of the edges themselves are arbitrary.
///
/// # Examples
///
/// ```
/// use graphalgs::connect::find_bridges;
/// use petgraph::graph::UnGraph;
///
/// // Create the following graph:
/// // 0----1    4
/// //      | __/|
/// // 5----2/---3
///
/// let mut g = UnGraph::new_undirected();
/// let n0 = g.add_node(());
/// let n1 = g.add_node(());
/// let n2 = g.add_node(());
/// let n3 = g.add_node(());
/// let n4 = g.add_node(());
/// let n5 = g.add_node(());
/// g.add_edge(n0, n1, ());
/// g.add_edge(n1, n2, ());
/// g.add_edge(n2, n3, ());
/// g.add_edge(n3, n4, ());
/// g.add_edge(n2, n4, ());
/// g.add_edge(n5, n2, ());
///
/// // The bridges in this graph are the undirected edges {2, 5}, {1, 2}, {0, 1}.
/// assert_eq!(find_bridges(&g), vec![(n2, n5), (n1, n2), (n0, n1)]);
/// ```
pub fn find_bridges<G>(graph: G) -> Vec<(G::NodeId, G::NodeId)>
where
    G: IntoNodeIdentifiers + IntoNeighbors + NodeIndexable,
{
    let mut bridges = Vec::new();
    let mut visited = vec![false; graph.node_bound()];
    let mut tin = vec![0usize; graph.node_bound()];
    let mut fup = vec![0usize; graph.node_bound()];
    let mut timer = 0usize;

    for start in 0..graph.node_bound() {
        if !visited[start] {
            dfs_helper(
                graph,
                start,
                graph.node_bound() + 1,
                &mut bridges,
                &mut visited,
                &mut timer,
                &mut tin,
                &mut fup,
            );
        }
    }

    bridges
}

#[allow(clippy::too_many_arguments)]
fn dfs_helper<G>(
    graph: G,
    v: usize,
    p: usize,
    bridges: &mut Vec<(G::NodeId, G::NodeId)>,
    visited: &mut Vec<bool>,
    timer: &mut usize,
    tin: &mut Vec<usize>,
    fup: &mut Vec<usize>,
) where
    G: IntoNodeIdentifiers + IntoNeighbors + NodeIndexable,
{
    visited[v] = true;
    *timer += 1;
    tin[v] = *timer;
    fup[v] = *timer;

    for n in graph.neighbors(graph.from_index(v)) {
        let to = graph.to_index(n);
        if to == p {
            continue;
        }
        if visited[to] {
            fup[v] = fup[v].min(tin[to]);
        } else {
            dfs_helper(graph, to, v, bridges, visited, timer, tin, fup);
            fup[v] = fup[v].min(fup[to]);
            if fup[to] > tin[v] {
                bridges.push((graph.from_index(v), graph.from_index(to)));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::UnGraph;

    #[test]
    fn test_find_bridges() {
        let mut g = UnGraph::<i8, i8>::new_undirected();
        assert_eq!(find_bridges(&g), vec![]);

        let n0 = g.add_node(0);
        assert_eq!(find_bridges(&g), vec![]);

        let n1 = g.add_node(1);
        assert_eq!(find_bridges(&g), vec![]);

        g.add_edge(n0, n1, 0);
        assert_eq!(find_bridges(&g), vec![(n0, n1)]);

        let n2 = g.add_node(2);
        assert_eq!(find_bridges(&g), vec![(n0, n1)]);

        g.add_edge(n2, n1, 1);
        g.add_edge(n0, n2, 2);
        assert_eq!(find_bridges(&g), vec![]);

        let n3 = g.add_node(3);
        let n4 = g.add_node(4);
        g.add_edge(n2, n3, 3);
        g.add_edge(n3, n4, 4);
        assert_eq!(find_bridges(&g), vec![(n3, n4), (n2, n3)]);

        g.add_edge(n3, n0, 5);
        assert_eq!(find_bridges(&g), vec![(n3, n4)]);

        let mut g = UnGraph::new_undirected();
        let n0 = g.add_node(());
        let n1 = g.add_node(());
        let n2 = g.add_node(());
        let n3 = g.add_node(());
        g.add_edge(n0, n2, ());
        g.add_edge(n2, n3, ());
        g.add_edge(n1, n3, ());

        assert_eq!(find_bridges(&g), vec![(n3, n1), (n2, n3), (n0, n2)]);

        let n4 = g.add_node(());
        let n5 = g.add_node(());
        let n6 = g.add_node(());
        let n7 = g.add_node(());
        g.add_edge(n4, n6, ());
        g.add_edge(n6, n7, ());
        g.add_edge(n5, n7, ());

        assert_eq!(
            find_bridges(&g),
            vec![(n3, n1), (n2, n3), (n0, n2), (n7, n5), (n6, n7), (n4, n6)]
        );

        g.add_edge(n5, n4, ());
        assert_eq!(find_bridges(&g), vec![(n3, n1), (n2, n3), (n0, n2)]);
    }
}
