use petgraph::visit::{IntoEdges, IntoNeighbors, IntoNodeIdentifiers, NodeCount, NodeIndexable};

/// Generate the [prufer code](https://en.wikipedia.org/wiki/Pr%C3%BCfer_sequence)
/// for a given [tree](https://en.wikipedia.org/wiki/Tree_(graph_theory)).
///
/// Before calling this function, make sure that the graph being called is
/// indeed a **tree**, otherwise stack overflow is possible.
///
/// # Example
///
/// ```
/// use graphalgs::spec::prufer_code;
/// use petgraph::graph::UnGraph;
/// use petgraph::visit::NodeIndexable;
///
/// let tree = UnGraph::<u8, ()>::from_edges(&[(0, 3), (0, 5), (3, 4), (3, 1), (3, 2)]);
///
/// // tree:
/// //
/// //     4
/// //     |
/// // 5-0-3-1
/// //     |
/// //     2
///
/// let ix = |i| tree.from_index(i);
/// assert_eq!(prufer_code(&tree), vec![ix(3), ix(3), ix(3), ix(0)]);
/// ```
pub fn prufer_code<G>(graph: G) -> Vec<G::NodeId>
where
    G: IntoEdges + IntoNodeIdentifiers + NodeCount + NodeIndexable + IntoNeighbors,
{
    let n = graph.node_count();
    if n <= 2 {
        return vec![];
    }

    let mut degree: Vec<usize> = vec![0; n];
    let mut leaf_ptr = None;

    for node in graph.node_identifiers() {
        let d = graph.neighbors(node).count();
        degree[graph.to_index(node)] = d;
        if d == 1 && leaf_ptr.is_none() {
            leaf_ptr = Some(graph.to_index(node));
        }
    }

    // for each vertex, we store the predecessor in a DFS with a start in node n-1.
    // For node n-1 we store the unreachable n+1.
    let mut parent: Vec<usize> = vec![n + 1; n];
    find_parents(graph, n - 1, &mut parent);

    let mut code: Vec<G::NodeId> = Vec::with_capacity(n - 2);
    let mut ptr = leaf_ptr.unwrap();
    let mut leaf_idx = ptr;

    for _ in 0..n - 2 {
        let next_idx = parent[leaf_idx];
        code.push(graph.from_index(next_idx));
        degree[next_idx] -= 1;
        if degree[next_idx] == 1 && next_idx < ptr {
            leaf_idx = next_idx;
        } else {
            ptr += 1;
            while degree[ptr] != 1 {
                ptr += 1;
            }
            leaf_idx = ptr;
        }
    }

    code
}

fn find_parents<G>(graph: G, node_idx: usize, parent: &mut Vec<usize>)
where
    G: IntoEdges + IntoNodeIdentifiers + NodeCount + NodeIndexable + IntoNeighbors,
{
    for n in graph.neighbors(graph.from_index(node_idx)) {
        let nx = graph.to_index(n);
        if nx != parent[node_idx] {
            parent[nx] = node_idx;
            find_parents(graph, nx, parent);
        }
    }
}

/// Restore a tree by its [prufer code](https://en.wikipedia.org/wiki/Pr%C3%BCfer_sequence).
///
/// The function returns a set of edges in any order,
/// the order of the vertex numbers in the edge does not matter.
/// If an impossible code is passed to the function, an empty vector is returned.
///
/// # Example
///
/// ```
/// use graphalgs::spec::prufer_decode;
///
/// // tree:
/// //
/// //     4
/// //     |
/// // 5-0-3-1
/// //     |
/// //     2
///
/// assert_eq!(
///     prufer_decode(&vec![3, 3, 3, 0]),
///     vec![(1, 3), (2, 3), (4, 3), (3, 0), (0, 5)]
/// );
///
/// assert_eq!(prufer_decode(&vec![0, 100]), vec![]); // Invalid code
/// ```
pub fn prufer_decode(code: &Vec<usize>) -> Vec<(usize, usize)> {
    let n = code.len() + 2;

    let mut degree: Vec<usize> = vec![1; n];
    for &node in code.iter() {
        if node > degree.len() {
            return vec![];
        }
        degree[node] += 1;
    }

    let mut ptr = 0;
    while degree[ptr] != 1 {
        ptr += 1;
    }
    let mut leaf = ptr;

    let mut edges: Vec<(usize, usize)> = Vec::with_capacity(n - 1);
    for &node in code.iter() {
        edges.push((leaf, node));
        degree[node] -= 1;
        if degree[node] == 1 && node < ptr {
            leaf = node;
        } else {
            ptr += 1;
            while degree[ptr] != 1 {
                ptr += 1;
            }
            leaf = ptr;
        }
    }
    edges.push((leaf, n - 1));
    edges
}

#[cfg(test)]
mod test {
    use super::*;
    use petgraph::graph::UnGraph;

    fn graph1() -> UnGraph<u8, f32> {
        let mut graph = UnGraph::<u8, f32>::new_undirected();
        let n0 = graph.add_node(0);
        let n1 = graph.add_node(1);
        let n2 = graph.add_node(2);
        let n3 = graph.add_node(3);
        let n4 = graph.add_node(4);
        let n5 = graph.add_node(5);
        let n6 = graph.add_node(6);
        let n7 = graph.add_node(7);
        let n8 = graph.add_node(8);
        let n9 = graph.add_node(9);

        graph.add_edge(n0, n1, 1.0);
        graph.add_edge(n0, n4, 2.0);
        graph.add_edge(n0, n6, 3.0);
        graph.add_edge(n6, n5, 4.0);
        graph.add_edge(n1, n2, 5.0);
        graph.add_edge(n1, n3, 6.0);
        graph.add_edge(n0, n9, 7.0);
        graph.add_edge(n9, n7, 8.0);
        graph.add_edge(n8, n9, 9.0);

        graph
    }

    fn graph2() -> UnGraph<u8, ()> {
        UnGraph::from_edges(&[(0, 1), (0, 2), (1, 3), (0, 4), (1, 5)])
    }

    fn graph3() -> UnGraph<u8, ()> {
        UnGraph::from_edges(&[(0, 3), (0, 5), (3, 4), (3, 1), (3, 2)])
    }

    fn graph4() -> UnGraph<u8, ()> {
        UnGraph::from_edges(&[(2, 0), (2, 1), (2, 3), (2, 4), (2, 5)])
    }

    #[test]
    fn test_prufer_code() {
        let graph = graph1();

        let ix = |i| graph.from_index(i);
        assert_eq!(
            prufer_code(&graph),
            vec![ix(1), ix(1), ix(0), ix(0), ix(6), ix(0), ix(9), ix(9)]
        );

        let graph = graph2();
        let ix = |i| graph.from_index(i);
        assert_eq!(prufer_code(&graph), vec![ix(0), ix(1), ix(0), ix(1)]);

        let graph = graph3();
        let ix = |i| graph.from_index(i);
        assert_eq!(prufer_code(&graph), vec![ix(3), ix(3), ix(3), ix(0)]);

        let graph = graph4();
        let ix = |i| graph.from_index(i);
        assert_eq!(prufer_code(&graph), vec![ix(2), ix(2), ix(2), ix(2)]);
    }

    #[test]
    fn test_prufer_decode() {
        assert_eq!(
            prufer_decode(&vec![1, 1, 0, 0, 6, 0, 9, 9]),
            vec![
                (2, 1),
                (3, 1),
                (1, 0),
                (4, 0),
                (5, 6),
                (6, 0),
                (0, 9),
                (7, 9),
                (8, 9)
            ],
        );
        assert_eq!(
            prufer_decode(&vec![0, 1, 0, 1]),
            vec![(2, 0), (3, 1), (4, 0), (0, 1), (1, 5)]
        );
        assert_eq!(
            prufer_decode(&vec![3, 3, 3, 0]),
            vec![(1, 3), (2, 3), (4, 3), (3, 0), (0, 5)]
        );
        assert_eq!(
            prufer_decode(&vec![2, 2, 2, 2]),
            vec![(0, 2), (1, 2), (3, 2), (4, 2), (2, 5)]
        );

        assert_eq!(prufer_decode(&vec![0, 1, 100, 200]), vec![]);
    }
}
