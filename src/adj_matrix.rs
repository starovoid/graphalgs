//! Graph adjacency matrices based on the [nalgebra](https://docs.rs/nalgebra/0.24.1/nalgebra/) crate.

use nalgebra::base::DMatrix;
use nalgebra::base::Scalar;

use petgraph::visit::{ IntoEdges, IntoNodeIdentifiers, GraphProp, EdgeRef,
                       IntoEdgeReferences, NodeCount, NodeIndexable };


/// Adjacency matrix of a simple graph.
/// 
/// If there is an edge from vertex i to vertex j, then cell (i, j) of the 
/// adjacency matrix will contain the value ```is_edge```, otherwise - ```no_edge```.
/// 
/// This matrix is designed for calculations using **nalgebra** so it can only contain types
/// with the ```Scalar``` trait. <a href="https://nalgebra.org/rustdoc/nalgebra/base/trait.Scalar.html">About Scalar</a>.
/// 
/// Note: the order of the matrix is equal to the maximum vertex index.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::adj_matrix::unweighted;
/// use petgraph::Graph;
/// use nalgebra::Matrix3;
/// 
/// let mut graph = Graph::new();
/// let a = graph.add_node('a');
/// let b = graph.add_node('b');
/// let c = graph.add_node('c');
/// graph.add_edge(a, b, 1.0);
/// graph.add_edge(a, c, 2.0);
/// graph.add_edge(c, b, 3.0);
///
/// let adj_m = unweighted(&graph, 1.0, 0.0);
/// assert_eq!(adj_m, Matrix3::new(0.0, 1.0, 1.0, 
///                                0.0, 0.0, 0.0, 
///                                0.0, 1.0, 0.0));
/// ```
pub fn unweighted<G, W>(graph: G, is_edge: W, no_edge: W) -> DMatrix<W>
    where 
        G: IntoEdges + IntoNodeIdentifiers + NodeCount + NodeIndexable, 
        W: Scalar + Copy,
{
    let mut adj_m = DMatrix::from_element(graph.node_bound(), graph.node_bound(), no_edge);

    for i in 0..graph.node_bound() {
        for j in graph.neighbors(graph.from_index(i)) {
            adj_m[(i, graph.to_index(j))] = is_edge;
        }
    }

    adj_m
}


/// Weighted adjacency matrix of a simple graph.
/// 
/// This matrix is designed for calculations using **nalgebra** so it can only contain types
/// with the ```Scalar``` trait. <a href="https://nalgebra.org/rustdoc/nalgebra/base/trait.Scalar.html">About Scalar</a>.
/// 
/// Note: the order of the matrix is equal to the maximum vertex index.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::adj_matrix::weighted;
/// use petgraph::Graph;
/// use nalgebra::Matrix3;
/// 
/// fn str_to_scalar(w: &&str) -> f64 {
///     w.parse().unwrap()
/// }
/// 
/// let mut graph = Graph::new();
/// let a = graph.add_node('a');
/// let b = graph.add_node('b');
/// let c = graph.add_node('c');
/// graph.add_edge(a, b, "1.0");
/// graph.add_edge(a, c, "2.0");
/// graph.add_edge(c, b, "3.0");
///
/// let adj_m = weighted(&graph, 0.0, str_to_scalar);
/// assert_eq!(adj_m, Matrix3::new(0.0, 1.0, 2.0, 
///                                0.0, 0.0, 0.0, 
///                                0.0, 3.0, 0.0));
/// ```
pub fn weighted<G, F, W>(graph: G, no_edge: W, mut edge_cost: F) -> DMatrix<W>
    where 
        G: IntoEdgeReferences + GraphProp + NodeCount + NodeIndexable, 
        F: FnMut(&G::EdgeWeight) -> W,
        W: Scalar + Copy,
{
    let mut adj_m = DMatrix::from_element(graph.node_bound(), graph.node_bound(), no_edge);
        
    for e in graph.edge_references() {
        let (i, j, w) = (e.source(), e.target(), e.weight());

        adj_m[(graph.to_index(i), graph.to_index(j))] = edge_cost(w);

        if !graph.is_directed() {
            adj_m[(graph.to_index(j), graph.to_index(i))] = edge_cost(w);
        }
    }

    adj_m
}


#[cfg(test)]
mod test {
    use super::*;
    use nalgebra::Matrix3;
    use petgraph::graph::Graph;
    use petgraph::graphmap::{ UnGraphMap, DiGraphMap };
    use petgraph::matrix_graph::MatrixGraph;
    use petgraph::stable_graph::StableGraph;
    use petgraph::csr::Csr;

    fn float_to_scalar(w: &f64) -> f64 {
        *w
    }

    fn str_to_scalar(w: &&str) -> f64 {
        w.parse().unwrap()
    }

    #[test]
    fn test_unweighted() {
        let graph = Graph::<char, f64>::new();
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, DMatrix::from_element(0, 0, 0.0));

        let mut graph = Graph::<char, f64>::new();
        graph.add_node('a');
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, DMatrix::from_element(1, 1, 0.0));

        let mut graph = Graph::new_undirected();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 1.0, 1.0, 0.0, 1.0, 1.0, 1.0, 0.0));

        let mut graph = Graph::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0));

        let mut graph = MatrixGraph::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1i64); graph.add_edge(a, c, 2i64); graph.add_edge(c, b, 3i64);
        let am = unweighted(&graph, true, false);
        assert_eq!(am, Matrix3::new(false, true, true, false, false, false, false, true, false));

        let mut graph = MatrixGraph::new_undirected();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 1.0, 1.0, 0.0, 1.0, 1.0, 1.0, 0.0));

        let mut graph = Csr::<char, f64>::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0));

        let mut graph = DiGraphMap::<char, f64>::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0));

        let mut graph = UnGraphMap::<char, f64>::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 1.0, 1.0, 0.0, 1.0, 1.0, 1.0, 0.0));

        let mut graph = StableGraph::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0));

        graph.remove_node(b);
        let am = unweighted(&graph, 1f64, 0f64);
        assert_eq!(am, Matrix3::new(0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0));
    }
    
    #[test]
    fn test_weighted() {
        let mut graph = Graph::new_undirected();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = weighted(&graph, 0f64, float_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 1.0, 0.0, 3.0, 2.0, 3.0, 0.0));

        let mut graph = Graph::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, "1.0"); graph.add_edge(a, c, "2.0"); graph.add_edge(c, b, "3.0");
        let am = weighted(&graph, 0f64, str_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0));

        let mut graph = MatrixGraph::new_undirected();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = weighted(&graph, 0f64, float_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 1.0, 0.0, 3.0, 2.0, 3.0, 0.0));

        let mut graph = MatrixGraph::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = weighted(&graph, 0f64, float_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0));

        let mut graph = UnGraphMap::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = weighted(&graph, 0f64, float_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 1.0, 0.0, 3.0, 2.0, 3.0, 0.0));

        let mut graph = DiGraphMap::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = weighted(&graph, 0f64, float_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0));

        let mut graph = Csr::<char, f64>::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, 1f64); graph.add_edge(a, c, 2f64); graph.add_edge(c, b, 3f64);
        let am = weighted(&graph, 0f64, float_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0));

        let mut graph = StableGraph::new();
        let a = graph.add_node('a'); let b = graph.add_node('b'); let c = graph.add_node('c');
        graph.add_edge(a, b, "1.0"); graph.add_edge(a, c, "2.0"); graph.add_edge(c, b, "3.0");
        let am = weighted(&graph, 0f64, str_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0));

        graph.remove_node(b);
        let am = weighted(&graph, 0f64, str_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 0.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0));
        graph.remove_node(a);
        let am = weighted(&graph, 0f64, str_to_scalar);
        assert_eq!(am, Matrix3::new(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0));
        graph.remove_node(c);
        let am = weighted(&graph, 0f64, str_to_scalar);
        assert_eq!(am, DMatrix::from_element(0, 0, 0.0));
    }
}
