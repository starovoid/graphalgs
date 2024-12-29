use nalgebra::base::DMatrix;
use nalgebra::base::Scalar;
use nalgebra::{ClosedAddAssign, ClosedSubAssign};
use num_traits::identities::Zero;

use petgraph::visit::{
    EdgeRef, GraphProp, IntoEdges, IntoNodeIdentifiers, NodeCount, NodeIndexable,
};

/// Laplacian (Kirchhoff) matrix of a graph.
///
/// - M[i, j] = -cost((i, j)) if i != j and (i, j) is in E(graph)
/// - M[i, i] = sum of cost((i, j)) over all edges (i, j) coming out of vertex i
/// - M[i, j] = 0 - otherwise
///
/// ## Arguments
/// * `graph`
/// * `edge_cost`: closure that returns cost of a particular edge.
///
/// ## Details
/// The algorithm treats multiple edges as distinct and ignores self-loops.
/// In an undirected graph, an undirected edge {i, j} is treated as a pair of edges (i, j) and (j, i).
///
/// This matrix is designed for calculations using **nalgebra** so it can only contain types
/// with the ```Scalar``` trait. [About Scalar](https://docs.rs/nalgebra/latest/nalgebra/base/trait.Scalar.html).
///
/// Note: the order of the matrix is equal to the maximum vertex index.
///
/// # Examples
///
/// ```
/// use graphalgs::spec::laplacian_matrix;
/// use petgraph::graph::{UnGraph, Graph};
/// use nalgebra::Matrix4;
///
/// // To begin with, let's look at working with an undirected graph.
/// let mut undir = UnGraph::<u32, f32>::new_undirected();
/// let n0 = undir.add_node(0);
/// let n1 = undir.add_node(1);
/// let n2 = undir.add_node(2);
/// let n3 = undir.add_node(3);
///
/// undir.add_edge(n0, n1, 10.0);
/// undir.add_edge(n1, n0, 10.0);
/// undir.add_edge(n2, n1, 20.0);
/// undir.add_edge(n3, n0, 30.0);
/// undir.add_edge(n2, n0, 40.0);
/// undir.add_edge(n2, n3, 50.0);
///
/// // Let's treat the graph as unweighted.
/// assert_eq!(
///     laplacian_matrix(&undir, |_| 1i32),
///     Matrix4::new(
///         4, -2, -1, -1,
///         -2, 3, -1, 0,
///         -1, -1, 3, -1,
///         -1, 0, -1, 2,
///     )
/// );
///
/// // As weighted.
/// assert_eq!(
///     laplacian_matrix(&undir, |edge| *edge.weight()),
///     Matrix4::new(
///         90.0, -20.0, -40.0, -30.0,
///         -20.0, 40.0, -20.0, 0.0,
///         -40.0, -20.0, 110.0, -50.0,
///         -30.0, 0.0, -50.0, 80.0,
///     )
/// );
///
///
/// // Now let's create a similar oriented graph.
/// let mut dir = Graph::<u32, f32>::new();
/// let d0 = dir.add_node(0);
/// let d1 = dir.add_node(1);
/// let d2 = dir.add_node(2);
/// let d3 = dir.add_node(3);
///
/// dir.add_edge(d0, d1, 10.0);
/// dir.add_edge(d1, d0, 10.0);
/// dir.add_edge(d2, d1, 20.0);
/// dir.add_edge(d3, d0, 30.0);
/// dir.add_edge(d2, d0, 40.0);
/// dir.add_edge(d2, d3, 50.0);
///
/// // Let's treat the graph as unweighted.
/// assert_eq!(
///     laplacian_matrix(&dir, |_| 1i32),
///     Matrix4::new(
///         1, -1, 0, 0,
///         -1, 1, 0, 0,
///         -1, -1, 3, -1,
///         -1, 0, 0, 1,
///     )
/// );
///
/// // As weighted.
/// assert_eq!(
///     laplacian_matrix(&dir, |edge| *edge.weight()),
///     Matrix4::new(
///         10.0, -10.0, 0.0, 0.0,
///         -10.0, 10.0, 0.0, 0.0,
///         -40.0, -20.0, 110.0, -50.0,
///         -30.0, 0.0, 0.0, 30.0,
///     )
/// );
/// ```
pub fn laplacian_matrix<G, F, W>(graph: G, mut edge_cost: F) -> DMatrix<W>
where
    G: IntoEdges + IntoNodeIdentifiers + NodeCount + NodeIndexable + GraphProp,
    F: FnMut(G::EdgeRef) -> W,
    W: Scalar + Copy + ClosedAddAssign + ClosedSubAssign + Zero,
{
    let mut kirch = DMatrix::from_element(graph.node_bound(), graph.node_bound(), W::zero());
    let mut diagonal = vec![W::zero(); graph.node_bound()];

    for e in graph.edge_references() {
        let (i, j) = (e.source(), e.target());
        let i = graph.to_index(i);
        let j = graph.to_index(j);
        if i == j {
            continue;
        }

        let cost = edge_cost(e);

        kirch[(i, j)] -= cost;
        diagonal[i] += cost;
        if !graph.is_directed() {
            kirch[(j, i)] -= cost;
            diagonal[j] += cost;
        }
    }

    for i in 0..graph.node_bound() {
        kirch[(i, i)] = diagonal[i];
    }

    kirch
}

#[cfg(test)]
mod test {
    use super::*;
    use nalgebra::Matrix4;
    use petgraph::graph::{Graph, UnGraph};

    #[test]
    fn test_laplacian_matrix_ungraph() {
        let mut graph = UnGraph::<u32, f32>::new_undirected();
        let n0 = graph.add_node(0);
        let n1 = graph.add_node(1);
        let n2 = graph.add_node(2);
        let n3 = graph.add_node(3);

        graph.add_edge(n0, n1, 10.0);
        graph.add_edge(n1, n2, 20.0);
        graph.add_edge(n0, n3, 30.0);
        graph.add_edge(n0, n2, 40.0);
        graph.add_edge(n3, n2, 50.0);

        assert_eq!(
            laplacian_matrix(&graph, |_| 1i32),
            Matrix4::new(3, -1, -1, -1, -1, 2, -1, 0, -1, -1, 3, -1, -1, 0, -1, 2,)
        );

        graph.add_edge(n1, n0, 10.0);
        assert_eq!(
            laplacian_matrix(&graph, |_| 1i32),
            Matrix4::new(4, -2, -1, -1, -2, 3, -1, 0, -1, -1, 3, -1, -1, 0, -1, 2,)
        );

        assert_eq!(
            laplacian_matrix(&graph, |edge| *edge.weight()),
            Matrix4::new(
                90.0, -20.0, -40.0, -30.0, -20.0, 40.0, -20.0, 0.0, -40.0, -20.0, 110.0, -50.0,
                -30.0, 0.0, -50.0, 80.0,
            )
        );
    }

    #[test]
    fn test_laplacian_matrix_digraph() {
        let mut digraph = Graph::<u32, f32>::new();
        let n0 = digraph.add_node(0);
        let n1 = digraph.add_node(1);
        let n2 = digraph.add_node(2);
        let n3 = digraph.add_node(3);

        digraph.add_edge(n0, n1, 10.0);
        digraph.add_edge(n2, n1, 20.0);
        digraph.add_edge(n3, n0, 30.0);
        digraph.add_edge(n2, n0, 40.0);
        digraph.add_edge(n2, n3, 50.0);

        assert_eq!(
            laplacian_matrix(&digraph, |_| 1i32),
            Matrix4::new(1, -1, 0, 0, 0, 0, 0, 0, -1, -1, 3, -1, -1, 0, 0, 1,)
        );

        digraph.add_edge(n1, n0, 10.0);
        assert_eq!(
            laplacian_matrix(&digraph, |_| 1i32),
            Matrix4::new(1, -1, 0, 0, -1, 1, 0, 0, -1, -1, 3, -1, -1, 0, 0, 1,)
        );

        assert_eq!(
            laplacian_matrix(&digraph, |edge| *edge.weight()),
            Matrix4::new(
                10.0, -10.0, 0.0, 0.0, -10.0, 10.0, 0.0, 0.0, -40.0, -20.0, 110.0, -50.0, -30.0,
                0.0, 0.0, 30.0,
            )
        );

        digraph.add_edge(n1, n1, 5.0);
        digraph.add_edge(n3, n3, 2.0);
        digraph.add_edge(n3, n3, 2.0);
        assert_eq!(
            laplacian_matrix(&digraph, |edge| *edge.weight()),
            Matrix4::new(
                10.0, -10.0, 0.0, 0.0, -10.0, 10.0, 0.0, 0.0, -40.0, -20.0, 110.0, -50.0, -30.0,
                0.0, 0.0, 30.0,
            )
        );
    }
}
