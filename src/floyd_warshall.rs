use std::hash::Hash;
use std::collections::HashMap;

use petgraph::visit::{ IntoEdgeReferences, NodeIndexable, IntoNodeIdentifiers, EdgeRef };
pub use petgraph::algo::FloatMeasure;


/// An algorithm error: a cycle of negative weights was found in the graph.
// In the current version of petgraph, the NegativeCycle structure contains a private field, 
// which prevents its public use. With the correction of this error, this definition will be removed.
#[derive(Clone, Debug, PartialEq)]
pub struct NegativeCycle(pub ());


/// [Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm) for all pairs shortest path problem.
///
/// Compute shortest paths in a weighted graph with positive or negative edge weights, but with no negative cycles.
/// Multiple edges and self-loops allowed.
///
/// ## Arguments
/// * `graph`: weighted graph.
/// * `edge_cost`: closure that returns cost of a particular edge.
///
/// ## Returns
/// * `Err`: if graph contains negative cycle.
/// * `Ok`: matrix `Vec<Vec<K>>` of shortest distances, in cell **(i, j)** of which the length of the shortest path 
///         from node **i** to node **j** is stored.
///
/// # Examples
/// 
/// ```
/// use graphalgs::floyd_warshall;
/// use petgraph::Graph;
/// 
/// let inf = f32::INFINITY;
/// 
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
///     (3, 2, 2.0), (2, 3, 20.0),
/// ]);
/// 
/// assert_eq!(
///     floyd_warshall(&graph, |edge| *edge.weight()),
///     Ok(vec![vec![0.0, 2.0, -1.0, -3.0],
///             vec![inf, 0.0, -3.0, -5.0],
///             vec![inf, inf,  0.0, 20.0],
///             vec![inf, inf,  2.0,  0.0]])
/// );
/// 
/// 
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)]);
/// 
/// assert!(floyd_warshall(&graph, |edge| *edge.weight()).is_err());
/// ```
pub fn floyd_warshall<G, F, K>(graph: G, mut edge_cost: F) -> Result<Vec<Vec<K>>, NegativeCycle>
    where
        G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable,
        F: FnMut(G::EdgeRef) -> K,
        K: FloatMeasure,
{
    let num_of_nodes = graph.node_bound();

    // Matrix of shortest distances.
    let mut dist = vec![vec![K::infinite(); num_of_nodes]; num_of_nodes];

    // Distance of each node to itself is 0.
    for i in graph.node_identifiers() {
        dist[graph.to_index(i)][graph.to_index(i)] = K::zero();
    }

    // Known distances between adjacent vertices.
    for edge in graph.edge_references() {
        let source = graph.to_index(edge.source());
        let target = graph.to_index(edge.target());
        let cost = edge_cost(edge);

        if cost < dist[source][target] {
            dist[source][target] = cost;
        }
    }

    for k in 0..num_of_nodes {
        for i in 0..num_of_nodes {
            for j in 0..num_of_nodes {
                if dist[i][k] + dist[k][j] < dist[i][j]{
                    dist[i][j] = dist[i][k] + dist[k][j];
                }
            }
        }
    }
    
    // If the distance from the node to itself has become negative, 
    // it means that there is a negative cycle in the graph.
    for i in 0..num_of_nodes {
        if dist[i][i] < K::zero() {
            return Err(NegativeCycle(()));
        }
    }

    Ok(dist)
}


/// Convert distance matrix into hashmap.
/// 
/// The algorithm takes as input the graph `graph` and the matrix of shortest distances `dist_matrix`, 
/// where cell **(i, j)** stores the shortest distance from node **i** to node **j**.
/// 
/// # Examples
/// 
/// ```
/// use std::collections::HashMap;
/// use graphalgs::{ floyd_warshall, distance_map };
/// use petgraph::prelude::NodeIndex;
/// use petgraph::visit::NodeIndexable;
/// use petgraph::Graph;
/// 
/// let inf = f32::INFINITY;
/// 
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
///     (3, 2, 2.0), (2, 3, 20.0),
/// ]);
/// 
/// let (n0, n1, n2, n3) = (graph.from_index(0), graph.from_index(1), 
///                         graph.from_index(2), graph.from_index(3));
/// 
/// let true_dist_map: HashMap<(NodeIndex, NodeIndex), f32> = [
///     ((n0, n0), 0.0), ((n0, n1), 2.0), ((n0, n2), -1.0), ((n0, n3), -3.0), 
///     ((n1, n0), inf), ((n1, n1), 0.0), ((n1, n2), -3.0), ((n1, n3), -5.0), 
///     ((n2, n0), inf), ((n2, n1), inf), ((n2, n2), 0.0),  ((n2, n3), 20.0), 
///     ((n3, n0), inf), ((n3, n1), inf), ((n3, n2), 2.0),  ((n3, n3), 0.0), 
/// ].iter().cloned().collect();
/// 
/// // Get the distance matrix.
/// let dist_matrix = floyd_warshall(&graph, |edge| *edge.weight()).unwrap();
/// 
/// // Convert the distance matrix into hashmap.
/// assert_eq!(distance_map(&graph, &dist_matrix), true_dist_map);
/// ```
pub fn distance_map<G, K>(graph: G, dist_matrix: &Vec<Vec<K>>) -> HashMap<(G::NodeId, G::NodeId), K>
    where G: NodeIndexable, 
          G::NodeId: Eq + Hash,
          K: FloatMeasure,
{
    let mut dist_map = HashMap::new();

    for (i, distances) in dist_matrix.iter().enumerate() {
        for (j, dist) in distances.iter().enumerate() {
            dist_map.insert((graph.from_index(i), graph.from_index(j)), *dist);
        }
    }

    dist_map
}


#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::{ Graph, NodeIndex };

    fn graph1() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(()); let n1 = graph.add_node(());
        let n2 = graph.add_node(()); let n3 = graph.add_node(());
        let n4 = graph.add_node(()); 

        graph.add_edge(n0, n1, 40.0); graph.add_edge(n0, n4, 18.0);
        graph.add_edge(n1, n0, 40.0); graph.add_edge(n1, n4, 15.0);
        graph.add_edge(n1, n2, 22.0); graph.add_edge(n1, n3, 6.0);
        graph.add_edge(n2, n1, 22.0); graph.add_edge(n2, n3, 14.0); 
        graph.add_edge(n3, n4, 20.0); graph.add_edge(n3, n1, 6.0);
        graph.add_edge(n3, n2, 14.0); graph.add_edge(n4, n0, 18.0);
        graph.add_edge(n4, n1, 15.0); graph.add_edge(n4, n3, 20.0);

        graph
    }

    fn graph2() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(()); let n1 = graph.add_node(());
        let n2 = graph.add_node(()); let n3 = graph.add_node(());
        let n4 = graph.add_node(()); let n5 = graph.add_node(()); 

        graph.add_edge(n0, n1, 1.0); graph.add_edge(n5, n1, -4.0);
        graph.add_edge(n1, n4, 5.0); graph.add_edge(n4, n1, 5.0);
        graph.add_edge(n2, n1, 8.0); graph.add_edge(n4, n3, 10.0);
        graph.add_edge(n3, n2, 0.0); graph.add_edge(n3, n2, -20.0);

        graph
    }

    fn graph3() -> Graph<(), f64> {
        let mut graph = Graph::<(), f64>::new();
        let n0 = graph.add_node(()); let n1 = graph.add_node(());
        let n2 = graph.add_node(()); let n3 = graph.add_node(());

        graph.add_edge(n0, n1, 10.0); graph.add_edge(n0, n2, 5.0);
        graph.add_edge(n1, n2, 2.0); graph.add_edge(n2, n3, -10.0);
        graph.add_edge(n3, n1, -1.0); graph.add_edge(n1, n3, 16.0);

        graph
    }

    fn graph4() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        graph.add_node(());
        graph
    }

    fn graph5() -> Graph<(), f32> { 
        Graph::<(), f32>::new() 
    }

    fn graph6() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(()); let n1 = graph.add_node(());
        let n2 = graph.add_node(());

        graph.add_edge(n0, n1, 1.0); graph.add_edge(n1, n0, -10.0);
        graph.add_edge(n2, n2, 5.0);
        graph
    }

    #[test]
    fn test_floyd_warshall() {
        let inf = f32::INFINITY;

        assert_eq!(
            floyd_warshall(&graph1(), |edge| *edge.weight()),
            Ok(vec![
                vec![0.0, 33.0, 52.0, 38.0, 18.0], vec![33.0, 0.0, 20.0, 6.0, 15.0], 
                vec![52.0, 20.0, 0.0, 14.0, 34.0], vec![38.0, 6.0, 14.0, 0.0, 20.0], 
                vec![18.0, 15.0, 34.0, 20.0, 0.0]
            ])
        );

        assert_eq!(
            floyd_warshall(&graph2(), |edge| *edge.weight()),
            Ok(vec![
                vec![0.0, 1.0, -4.0, 16.0, 6.0, inf], vec![inf, 0.0, -5.0, 15.0, 5.0, inf], 
                vec![inf, 8.0, 0.0, 23.0, 13.0, inf], vec![inf, -12.0, -20.0, 0.0, -7.0, inf], 
                vec![inf, -2.0, -10.0, 10.0, 0.0, inf], vec![inf, -4.0, -9.0, 11.0, 1.0, 0.0],
            ])
        );
        
        // Graphs with negative cycle
        assert_eq!(floyd_warshall(&graph3(), |edge| *edge.weight()), Err(NegativeCycle(())));
        assert_eq!(floyd_warshall(&graph6(), |edge| *edge.weight()), Err(NegativeCycle(())));
        
        let mut graph = graph1();
        graph.add_edge(3.into(), 3.into(), -5.0);
        assert_eq!(floyd_warshall(&graph, |edge| *edge.weight()), Err(NegativeCycle(())));
        
        // Edge cases
        assert_eq!(floyd_warshall(&graph4(), |edge| *edge.weight()), Ok(vec![vec![0.0]]));
        assert_eq!(floyd_warshall(&graph5(), |edge| *edge.weight()), Ok(vec![]));
    }
    
    #[test]
    fn test_distance_map() {
        let graph = graph5();
        let dist_matrix = floyd_warshall(&graph, |edge| *edge.weight()).unwrap();
        assert_eq!(distance_map(&graph, &dist_matrix), HashMap::new());


        let graph = graph4();
        let mut true_dist_map = HashMap::new();
        true_dist_map.insert((graph.from_index(0), graph.from_index(0)), 0.0);

        let dist_matrix = floyd_warshall(&graph, |edge| *edge.weight()).unwrap();
        assert_eq!(distance_map(&graph, &dist_matrix), true_dist_map);


        let graph = graph1();
        let true_dist_map: HashMap<(NodeIndex, NodeIndex), f32> = [
            ((0.into(), 0.into()), 0.0), ((0.into(), 1.into()), 33.0), ((0.into(), 2.into()), 52.0), 
            ((0.into(), 3.into()), 38.0), ((0.into(), 4.into()), 18.0), ((1.into(), 0.into()), 33.0), 
            ((1.into(), 1.into()), 0.0), ((1.into(), 2.into()), 20.0), ((1.into(), 3.into()), 6.0), 
            ((1.into(), 4.into()), 15.0), ((2.into(), 0.into()), 52.0), ((2.into(), 1.into()), 20.0), 
            ((2.into(), 2.into()), 0.0), ((2.into(), 3.into()), 14.0), ((2.into(), 4.into()), 34.0), 
            ((3.into(), 0.into()), 38.0), ((3.into(), 1.into()), 6.0), ((3.into(), 2.into()), 14.0), 
            ((3.into(), 3.into()), 0.0), ((3.into(), 4.into()), 20.0), ((4.into(), 0.into()), 18.0), 
            ((4.into(), 1.into()), 15.0), ((4.into(), 2.into()), 34.0), ((4.into(), 3.into()), 20.0), 
            ((4.into(), 4.into()), 0.0), 
        ].iter().cloned().collect();
        
        let dist_matrix = floyd_warshall(&graph, |edge| *edge.weight()).unwrap();
        assert_eq!(distance_map(&graph, &dist_matrix), true_dist_map);
    }
}
