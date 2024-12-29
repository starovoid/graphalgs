use petgraph::visit::{IntoNeighbors, IntoNodeIdentifiers, NodeIndexable};

/// Find all articulation points in a simple undirected graph.
///
/// In a graph, a vertex is called an articulation point if removing it and all the edges
/// associated with it results in the increase of the number of connected components in the graph.
///
/// Returns the vector of `G::NodeID`.
///
/// # Examples
///
/// ```
/// use graphalgs::connect::articulation_points;
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
/// // The articulation points of this graph are vertices 1 and 2.
/// assert_eq!(articulation_points(&g), vec![n2, n1]);
/// ```
pub fn articulation_points<G>(graph: G) -> Vec<G::NodeId>
where
    G: IntoNodeIdentifiers + IntoNeighbors + NodeIndexable,
{
    let mut cut_points = Vec::new();
    let mut visited = vec![false; graph.node_bound()];
    let mut is_cut_point = vec![false; graph.node_bound()];
    let mut tin = vec![0usize; graph.node_bound()];
    let mut fup = vec![0usize; graph.node_bound()];
    let mut timer = 0usize;

    for start in 0..graph.node_bound() {
        if !visited[start] {
            dfs_helper(
                graph,
                start,
                graph.node_bound() + 1,
                &mut is_cut_point,
                &mut cut_points,
                &mut visited,
                &mut timer,
                &mut tin,
                &mut fup,
            );
        }
    }

    cut_points
}

#[allow(clippy::too_many_arguments)]
fn dfs_helper<G>(
    graph: G,
    v: usize,
    p: usize,
    is_cut_point: &mut Vec<bool>,
    cut_points: &mut Vec<G::NodeId>,
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
    let mut children = 0usize;

    for n in graph.neighbors(graph.from_index(v)) {
        let to = graph.to_index(n);
        if to == p {
            continue;
        }
        if visited[to] {
            fup[v] = fup[v].min(tin[to]);
        } else {
            dfs_helper(
                graph,
                to,
                v,
                is_cut_point,
                cut_points,
                visited,
                timer,
                tin,
                fup,
            );
            fup[v] = fup[v].min(fup[to]);
            if fup[to] >= tin[v] && p < graph.node_bound() && !is_cut_point[v] {
                is_cut_point[v] = true;
                cut_points.push(graph.from_index(v));
            }
            children += 1;
        }
    }

    if p > graph.node_bound() && children > 1 && !is_cut_point[v] {
        is_cut_point[v] = true;
        cut_points.push(graph.from_index(v));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::UnGraph;

    #[test]
    fn test_articulation_points_case_1() {
        let mut g = UnGraph::<i8, i8>::new_undirected();
        assert_eq!(articulation_points(&g), vec![]);

        let n0 = g.add_node(0);
        assert_eq!(articulation_points(&g), vec![]);

        let n1 = g.add_node(1);
        assert_eq!(articulation_points(&g), vec![]);

        g.add_edge(n0, n1, 0);
        assert_eq!(articulation_points(&g), vec![]);

        let n2 = g.add_node(2);
        assert_eq!(articulation_points(&g), vec![]);

        g.add_edge(n2, n1, 1);
        g.add_edge(n0, n2, 2);
        assert_eq!(articulation_points(&g), vec![]);

        let n3 = g.add_node(3);
        let n4 = g.add_node(4);
        g.add_edge(n2, n3, 3);
        g.add_edge(n3, n4, 4);
        assert_eq!(articulation_points(&g), vec![n3, n2]);

        g.add_edge(n3, n0, 5);
        assert_eq!(articulation_points(&g), vec![n3]);
    }

    #[test]
    fn test_articulation_points_case_2() {
        let mut g = UnGraph::new_undirected();
        let n0 = g.add_node(());
        let n1 = g.add_node(());
        let n2 = g.add_node(());
        let n3 = g.add_node(());
        g.add_edge(n0, n2, ());
        g.add_edge(n2, n3, ());
        g.add_edge(n1, n3, ());

        assert_eq!(articulation_points(&g), vec![n3, n2]);

        let n4 = g.add_node(());
        let n5 = g.add_node(());
        let n6 = g.add_node(());
        let n7 = g.add_node(());
        g.add_edge(n4, n6, ());
        g.add_edge(n6, n7, ());
        g.add_edge(n5, n7, ());

        assert_eq!(articulation_points(&g), vec![n3, n2, n7, n6]);

        g.add_edge(n5, n4, ());
        assert_eq!(articulation_points(&g), vec![n3, n2]);

        let n8 = g.add_node(());
        g.add_edge(n3, n8, ());
        g.add_edge(n5, n8, ());
        assert_eq!(articulation_points(&g), vec![n5, n8, n3, n2]);

        let n9 = g.add_node(());
        g.add_edge(n4, n9, ());
        assert_eq!(articulation_points(&g), vec![n4, n5, n8, n3, n2]);

        g.add_edge(n1, n9, ());
        assert_eq!(articulation_points(&g), vec![n3, n2]);

        g.add_edge(n1, n0, ());
        assert_eq!(articulation_points(&g), vec![]);
    }
}
