use crate::adj_matrix::unweighted;
use nalgebra::base::{dimension::Dyn, DMatrix, Scalar};
use nalgebra::{ClosedAddAssign, ClosedMulAssign};
use num_traits::identities::{One, Zero};
use petgraph::visit::{IntoEdges, IntoNodeIdentifiers, NodeCount, NodeIndexable};
use std::ops::Sub;

/// [Seidel's algorithm (APD)](https://en.wikipedia.org/wiki/Seidel%27s_algorithm)
/// for all pairs shortest path problem.
///
/// Compute the matrix of shortest distances of an **unweighted**, **undirected**, **connected** graph.
///
/// This function works under the assumption that the maximum distance between vertices
/// does not exceed `u32::MAX`. If you want more control over data types use the `apd()` function.
///
/// # Examples
///
/// ```
/// use graphalgs::shortest_path::seidel;
/// use petgraph::Graph;
///
/// let mut graph: Graph<(), ()> = Graph::new();
/// let n0 = graph.add_node(()); // Node with no weight
/// let n1 = graph.add_node(());
/// let n2 = graph.add_node(());
/// let n3 = graph.add_node(());
/// let n4 = graph.add_node(());
/// let n5 = graph.add_node(());
/// graph.extend_with_edges(&[
///     (0, 1), (1, 0),  // A pair of two directed edges forms one undirected edge
///     (0, 3), (3, 0),
///     (1, 2), (2, 1),
///     (1, 5), (5, 1),
///     (2, 4), (4, 2),
///     (3, 4), (4, 3),
///     (4, 5), (5, 4),
/// ]);
///
/// // Graph representation
/// //
/// // (0)-----(1)-----(2)
/// //  |       |       |
/// // (3)     (5)      |
/// //  |       |       |
/// //  \------(4)------/
///
/// // Graph distance matrix.
/// // At position (i, j) the length of the path from vertex i to vertex j.
/// assert_eq!(
///     seidel(&graph),
///     vec![vec![0, 1, 2, 1, 2, 2],
///          vec![1, 0, 1, 2, 2, 1],
///          vec![2, 1, 0, 2, 1, 2],
///          vec![1, 2, 2, 0, 1, 2],
///          vec![2, 2, 1, 1, 0, 1],
///          vec![2, 1, 2, 2, 1, 0]]
/// );
pub fn seidel<G>(graph: G) -> Vec<Vec<u32>>
where
    G: IntoEdges + IntoNodeIdentifiers + NodeCount + NodeIndexable,
{
    apd(unweighted(graph, 1u32, 0u32))
        .row_iter()
        .map(|row| row.into_iter().copied().collect())
        .collect()
}

/// [APD algorithm](https://en.wikipedia.org/wiki/Seidel%27s_algorithm)
/// for all pairs shortest path problem.
///
/// Compute the matrix of shortest distances of an **unweighted**, **undirected**, **connected** graph.
///
/// Unlike `seidel`, this function takes an adjacency matrix as input,
/// which can be constructed, for example, using `graphalgs::adj_matrix::unweighted`.
/// Use this algorithm if you need more control over data types or you already have an adjacency matrix.
///
/// # Examples
///
/// ```
/// use graphalgs::shortest_path::apd;
/// use graphalgs::adj_matrix;
/// use petgraph::Graph;
/// use nalgebra::Matrix6;
///
/// let mut graph: Graph<(), ()> = Graph::new();
/// let n0 = graph.add_node(()); // Node with no weight
/// let n1 = graph.add_node(());
/// let n2 = graph.add_node(());
/// let n3 = graph.add_node(());
/// let n4 = graph.add_node(());
/// let n5 = graph.add_node(());
/// graph.extend_with_edges(&[
///     (0, 1), (1, 0),  // A pair of two directed edges forms one undirected edge
///     (0, 3), (3, 0),
///     (1, 2), (2, 1),
///     (1, 5), (5, 1),
///     (2, 4), (4, 2),
///     (3, 4), (4, 3),
///     (4, 5), (5, 4),
/// ]);
///
/// // Graph representation
/// //
/// // (0)-----(1)-----(2)
/// //  |       |       |
/// // (3)     (5)      |
/// //  |       |       |
/// //  \------(4)------/
///
/// // Graph diameter is two, so we can use u8 to calculate the distances between the vertices.
/// let matrix = adj_matrix::unweighted(&graph, 1u8, 0u8);
///
/// // Graph distance matrix.
/// // At position (i, j) the length of the path from vertex i to vertex j.
/// assert_eq!(
///     apd(matrix),
///     Matrix6::new(
///         0, 1, 2, 1, 2, 2,
///         1, 0, 1, 2, 2, 1,
///         2, 1, 0, 2, 1, 2,
///         1, 2, 2, 0, 1, 2,
///         2, 2, 1, 1, 0, 1,
///         2, 1, 2, 2, 1, 0,
///     )
/// );
#[allow(non_snake_case)]
pub fn apd<K>(A: DMatrix<K>) -> DMatrix<K>
where
    K: Scalar
        + Copy
        + ClosedAddAssign
        + ClosedMulAssign
        + Zero
        + One
        + PartialOrd
        + Sub<K, Output = K>,
{
    let n = A.nrows();
    let nrows = Dyn(n);
    let ncols = Dyn(n);
    if (0..n).all(|i| (0..n).all(|j| i == j || A[(i, j)] != K::zero())) {
        return A;
    }

    unsafe {
        let mut Z = DMatrix::uninit(nrows, ncols).assume_init();
        A.mul_to(&A, &mut Z);

        let mut B = DMatrix::uninit(nrows, ncols).assume_init();
        for i in 0..n {
            for j in 0..n {
                if i != j && (A[(i, j)] == K::one() || Z[(i, j)] > K::zero()) {
                    B[(i, j)] = K::one();
                } else {
                    B[(i, j)] = K::zero();
                }
            }
        }

        let T = apd(B);
        let mut X = DMatrix::uninit(nrows, ncols).assume_init();
        T.mul_to(&A, &mut X);

        let degree = A.row_iter().map(|row| row.sum()).collect::<Vec<K>>();

        let mut D = DMatrix::uninit(nrows, ncols).assume_init();
        for i in 0..n {
            for j in 0..n {
                if X[(i, j)] >= T[(i, j)] * degree[j] {
                    D[(i, j)] = T[(i, j)] + T[(i, j)];
                } else {
                    D[(i, j)] = T[(i, j)] + T[(i, j)] - K::one();
                }
            }
        }

        D
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::random_ungraph;
    use crate::shortest_path::floyd_warshall;
    use petgraph::graph::Graph;
    use petgraph::Directed;
    use rand::Rng;

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

    fn graph2() -> Graph<(), ()> {
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
        graph.add_edge(n2, n3, ());
        graph.add_edge(n3, n2, ());

        graph
    }

    fn graph3() -> Graph<(), f64> {
        let mut graph = Graph::<(), f64>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        graph.add_edge(n0, n1, 10.0);
        graph.add_edge(n1, n0, 5.0);
        graph
    }

    fn graph4() -> Graph<(), f32> {
        Graph::<(), f32>::new()
    }

    #[test]
    fn test_apd() {
        assert_eq!(
            apd(unweighted(&graph1(), 1u8, 0u8))
                .row_iter()
                .map(|row| row.into_iter().copied().collect::<Vec<u8>>())
                .collect::<Vec<Vec<u8>>>(),
            vec![
                vec![0, 1, 2, 2, 1],
                vec![1, 0, 1, 1, 1],
                vec![2, 1, 0, 1, 2],
                vec![2, 1, 1, 0, 1],
                vec![1, 1, 2, 1, 0]
            ]
        );

        assert_eq!(
            apd(unweighted(&graph2(), 1usize, 0usize))
                .row_iter()
                .map(|row| row.into_iter().copied().collect::<Vec<usize>>())
                .collect::<Vec<Vec<usize>>>(),
            vec![
                vec![0, 1, 2, 2],
                vec![1, 0, 1, 1],
                vec![2, 1, 0, 1],
                vec![2, 1, 1, 0],
            ]
        );

        // Edge cases
        assert_eq!(
            apd(unweighted(&graph3(), 1f64, 0.0))
                .row_iter()
                .map(|row| row.into_iter().copied().collect::<Vec<f64>>())
                .collect::<Vec<Vec<f64>>>(),
            vec![vec![0.0, 1.0], vec![1.0, 0.0]]
        );

        assert_eq!(
            apd(unweighted(&graph4(), 1f32, 0.0))
                .row_iter()
                .map(|row| row.into_iter().copied().collect::<Vec<f32>>())
                .collect::<Vec<Vec<f32>>>(),
            Vec::<Vec<f32>>::new()
        );

        // Random tests
        let mut rng = rand::thread_rng();

        for n in 2..=50 {
            let graph = Graph::<(), f32, Directed, usize>::from_edges(
                random_ungraph(
                    n,
                    rng.gen_range((n - 1) * (n - 2) / 2 + 1..=n * (n - 1) / 2),
                )
                .unwrap()
                .into_iter()
                .map(|edge| (edge.0, edge.1, 1.0)),
            );

            assert_eq!(
                apd(unweighted(&graph, 1f32, 0.0))
                    .row_iter()
                    .map(|row| row.into_iter().copied().collect::<Vec<f32>>())
                    .collect::<Vec<Vec<f32>>>(),
                floyd_warshall(&graph, |edge| *edge.weight()).unwrap()
            );
        }
    }

    #[test]
    fn test_seidel() {
        assert_eq!(
            seidel(&graph1()),
            vec![
                vec![0, 1, 2, 2, 1],
                vec![1, 0, 1, 1, 1],
                vec![2, 1, 0, 1, 2],
                vec![2, 1, 1, 0, 1],
                vec![1, 1, 2, 1, 0]
            ]
        );

        assert_eq!(
            seidel(&graph2()),
            vec![
                vec![0, 1, 2, 2],
                vec![1, 0, 1, 1],
                vec![2, 1, 0, 1],
                vec![2, 1, 1, 0],
            ]
        );

        // Edge cases
        assert_eq!(seidel(&graph3()), vec![vec![0, 1], vec![1, 0]]);
        assert_eq!(seidel(&graph4()), Vec::<Vec<u32>>::new());

        // Random tests
        let mut rng = rand::thread_rng();

        for n in 2..=50 {
            let graph = Graph::<(), f32, Directed, usize>::from_edges(
                random_ungraph(
                    n,
                    rng.gen_range((n - 1) * (n - 2) / 2 + 1..=n * (n - 1) / 2),
                )
                .unwrap()
                .into_iter()
                .map(|edge| (edge.0, edge.1, 1.0)),
            );

            assert_eq!(
                seidel(&graph)
                    .into_iter()
                    .map(|row| row.into_iter().map(|d| d as f32).collect::<Vec<f32>>())
                    .collect::<Vec<Vec<f32>>>(),
                floyd_warshall(&graph, |edge| *edge.weight()).unwrap()
            );
        }
    }
}
