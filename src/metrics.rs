//! Basic graph characteristics based on the concept of distance between vertices.

use petgraph::visit::{ 
    Visitable, NodeIndexable, IntoEdges, IntoEdgeReferences, 
    IntoNeighbors, IntoNodeIdentifiers, NodeCount, 
};
use petgraph::algo::{ FloatMeasure, bellman_ford };
use crate::shortest_path::{ shortest_distances, floyd_warshall };

/// Vertex eccentricity.
/// 
/// Calculate the eccentricity of a vertex ```node``` of the graph ```graph```.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::eccentricity;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), ()>::from_edges(&[(0, 1), (1, 0), (1, 2)]);
/// 
/// assert_eq!(eccentricity(&graph, 0.into()), 2.0);
/// assert_eq!(eccentricity(&graph, 1.into()), 1.0);
/// assert_eq!(eccentricity(&graph, 2.into()), f32::INFINITY);
/// ```
pub fn eccentricity<G>(graph: G, node: G::NodeId) -> f32 
where 
    G: Visitable + NodeIndexable + IntoEdges + IntoNeighbors 
{
    *shortest_distances(graph, node)
        .iter()
        .max_by(|x, y| x.partial_cmp(&y).unwrap())
        .unwrap()
}


/// Graph radius.
/// 
/// Calculate the radius of a graph ```graph```. 
/// Returns ```Option<f32>```, ```None``` will be in case there are no vertices in the graph.
/// If the graph radius is infinity, then the result of the algorithm will be ```f32::INFINITY```.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::radius;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), ()>::from_edges(&[(0, 1), (1, 0), (1, 2)]);
/// 
/// assert_eq!(radius(&graph), Some(1.0));
/// ```
pub fn radius<G>(graph: G) -> Option<f32> 
where 
    G: Visitable + NodeIndexable + IntoEdges + IntoNeighbors + IntoNodeIdentifiers + NodeCount
{
    if graph.node_count() == 0 {
        return None;
    }

    graph.node_identifiers()
        .map(|i| eccentricity(graph, i))
        .min_by(|x, y| x.partial_cmp(&y).unwrap())
}


/// Graph diameter.
/// 
/// Calculate the diameter of a graph ```graph```. 
/// Returns ```Option<f32>```, ```None``` will be in case there are no vertices in the graph.
/// If the graph diameter is infinity, then the result of the algorithm will be ```f32::INFINITY```.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::diameter;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), ()>::from_edges(&[(0, 1), (1, 0), (1, 2)]);
/// 
/// assert_eq!(diameter(&graph), Some(f32::INFINITY));
/// ```
pub fn diameter<G>(graph: G) -> Option<f32> 
where 
    G: Visitable + NodeIndexable + IntoEdges + IntoNeighbors + IntoNodeIdentifiers + NodeCount
{
    if graph.node_count() == 0 {
        return None;
    }

    let mut diam = 0f32;
    for i in graph.node_identifiers() {
        diam = diam.max(eccentricity(graph, i));
        if diam == f32::INFINITY {
            break;
        }
    }

    Some(diam)
}


/// Central vertices of the graph.
/// 
/// Returns a vector of indices of the central vertices of the graph.
/// Here, the central vertices are the vertices with the minimum eccentricity.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::center;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), ()>::from_edges(&[(0, 1), (1, 0), (1, 2)]);
/// 
/// assert_eq!(center(&graph), vec![1.into()]);
/// ```
pub fn center<G>(graph: G) -> Vec<G::NodeId>
where 
    G: Visitable + NodeIndexable + IntoEdges + IntoNodeIdentifiers
{   
    // Vector of vertex eccentricities to avoid repeated computation.
    let ecc = graph.node_identifiers()
        .map(|i| eccentricity(graph, i))
        .collect::<Vec<f32>>();
    
    match ecc.iter().min_by(|x, y| x.partial_cmp(&y).unwrap()) {
        None => vec![],
        Some(&r) => {
            graph.node_identifiers()
                .enumerate()
                .filter(|(i, _)| ecc[*i] == r)
                .map(|(_, node_id)| node_id)
                .collect()
        },
    }
}


/// Peripheral graph vertices.
/// 
/// Returns a vector of indices of the peripheral vertices of the graph.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::periphery;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), ()>::from_edges(&[(0, 1), (1, 0), (1, 2)]);
/// 
/// assert_eq!(periphery(&graph), vec![2.into()]);
/// ```
pub fn periphery<G>(graph: G) -> Vec<G::NodeId>
where 
    G: Visitable + NodeIndexable + IntoEdges + IntoNodeIdentifiers
{ 
    // Vector of vertex eccentricities to avoid repeated computation.
    let ecc = graph.node_identifiers()
        .map(|i| eccentricity(graph, i))
        .collect::<Vec<f32>>();
    
    match ecc.iter().max_by(|x, y| x.partial_cmp(&y).unwrap()) {
        None => vec![],   // There are no vertices in the graph.
        Some(&d) => graph.node_identifiers()
            .enumerate()
            .filter(|(i, _)| ecc[*i] == d)
            .map(|(_, node_id)| node_id)
            .collect()
    }
}


/// Weighted eccentricity.
/// 
/// Calculate the distance to the node farthest from `start`, given the edge weights.
/// The function is based on the [Bellman-Ford algorithm](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm)
/// and has a time complexity of **O(|V|*|E|)**. So if edge weight is not important it is better to use `eccentricity()` function.
/// 
/// ## Arguments
/// * `graph`: weighted graph.
/// * `start`: node whose eccentricity is to be calculated.
///
/// ## Returns
/// * `Some(G::EdgeWeight)`: the eccentricity.
/// * `None`: if graph contains negative cycle.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::weighted_eccentricity;
/// use petgraph::Graph;
/// 
/// let inf = f32::INFINITY;
/// 
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
///     (3, 2, 2.0), (2, 3, 20.0),
/// ]);
/// 
/// assert_eq!(weighted_eccentricity(&graph, 0.into()), Some(2.0));
/// assert_eq!(weighted_eccentricity(&graph, 1.into()), Some(inf));
/// assert_eq!(weighted_eccentricity(&graph, 2.into()), Some(inf));
/// assert_eq!(weighted_eccentricity(&graph, 3.into()), Some(inf));
/// 
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)
/// ]);
/// 
/// assert_eq!(weighted_eccentricity(&graph, 0.into()), None);
/// assert_eq!(weighted_eccentricity(&graph, 1.into()), None);
/// assert_eq!(weighted_eccentricity(&graph, 2.into()), None);
/// ```
pub fn weighted_eccentricity<G>(graph: G, start: G::NodeId) -> Option<G::EdgeWeight>
where
    G: NodeCount + IntoNodeIdentifiers + IntoEdges + NodeIndexable,
    G::EdgeWeight: FloatMeasure,
{
    let distances = bellman_ford(graph, start);
    
    if distances.is_err() {
        return None;  // The graph contains a negative cycle.
    }

    Some(*distances.unwrap().0
            .iter()
            .max_by(|x, y| x.partial_cmp(&y).unwrap())
            .unwrap())
}


/// Weighted graph radius.
/// 
/// Calculate the radius of the graph given the edge weights. 
/// The function is based on the [Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm)
/// and has a time complexity of **O(|V|^3)**. 
/// So if edge weights is not important it is better to use `radius()` function.
/// 
/// ## Arguments
/// * `graph`: weighted graph.
/// * `edge_cost`: closure that returns weight of a particular edge.
///
/// ## Returns
/// * `Some`: the radius of the graph. 
/// * `None`: if the graph contains a negative cycle or has no vertices.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::weighted_radius;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
///     (3, 2, 2.0), (2, 3, 20.0),
/// ]);
/// 
/// assert_eq!(weighted_radius(&graph, |edge| *edge.weight()), Some(2.0));
/// 
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)
/// ]);
/// 
/// assert_eq!(weighted_radius(&graph, |edge| *edge.weight()), None);
/// ```
pub fn weighted_radius<G, F, K>(graph: G, edge_cost: F) -> Option<K>
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure,
{
    if graph.node_count() == 0 {
        return None;
    }

    let distances = floyd_warshall(graph, edge_cost);

    if distances.is_err() {
        return None;  // The graph contains a negative cycle.
    }

    distances.unwrap()
        .iter()
        .map(|dist| *dist.iter().max_by(|x, y| x.partial_cmp(&y).unwrap()).unwrap())
        .min_by(|x, y| x.partial_cmp(&y).unwrap())
}


/// Weighted graph diameter.
/// 
/// Calculate the diameter of the graph given the edge weights. 
/// The function is based on the [Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm)
/// and has a time complexity of **O(|V|^3)**. 
/// So if edge weights is not important it is better to use `diameter()` function.
/// 
/// ## Arguments
/// * `graph`: weighted graph.
/// * `edge_cost`: closure that returns weight of a particular edge.
///
/// ## Returns
/// * `Some`: the diameter of the graph. 
/// * `None`: if the graph contains a negative cycle or has no vertices.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::metrics::weighted_diameter;
/// use petgraph::Graph;
/// 
/// let inf = f32::INFINITY;
/// 
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
///     (3, 2, 2.0), (2, 3, 20.0),
/// ]);
/// 
/// assert_eq!(weighted_diameter(&graph, |edge| *edge.weight()), Some(inf));
/// 
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)
/// ]);
/// 
/// assert_eq!(weighted_diameter(&graph, |edge| *edge.weight()), None);
/// ```
pub fn weighted_diameter<G, F, K>(graph: G, edge_cost: F) -> Option<K>
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure,
{
    if graph.node_count() == 0 {
        return None;
    }

    let distances = floyd_warshall(graph, edge_cost);

    if distances.is_err() {
        return None;  // The graph contains a negative cycle.
    }

    let mut diam = K::zero();
    for dist in distances.unwrap().iter() {
        for d in dist.iter() {
            if *d == K::infinite() {
                return Some(*d);
            } else if *d > diam {
                diam = *d;
            }
        }
    }

    Some(diam)
}


/// Center of a weighted graph.
/// 
/// Calculate the central nodes of the graph given the edge weights. 
/// The function is based on the [Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm)
/// and has a time complexity of **O(|V|^3)**. 
/// So if edge weights is not important it is better to use `center()` function.
/// 
/// ## Arguments
/// * `graph`: weighted graph.
/// * `edge_cost`: closure that returns weight of a particular edge.
///
/// ## Returns
/// * A vector of indices of central vertices.
/// * `vec![]`: if the graph contains a negative cycle.
/// 
/// ```
/// use graphalgs::metrics::weighted_center;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
///     (3, 2, 2.0), (2, 3, 20.0), (3, 0, 3.0),
/// ]);
/// 
/// assert_eq!(weighted_center(&graph, |edge| *edge.weight()), vec![1.into()]);
/// 
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)
/// ]);
/// 
/// assert_eq!(weighted_center(&graph, |edge| *edge.weight()), vec![]);
/// ```
pub fn weighted_center<G, F, K>(graph: G, edge_cost: F) -> Vec<G::NodeId>
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure,
{
    if graph.node_count() == 0 {
        return vec![];
    }

    let distances = floyd_warshall(graph, edge_cost);

    if distances.is_err() {
        return vec![];  // The graph contains a negative cycle.
    }
    
    // Vector of node eccentricities.
    let ecc = distances.unwrap()
        .iter()
        .map(|dist| *dist.iter().max_by(|x, y| x.partial_cmp(&y).unwrap()).unwrap())
        .collect::<Vec<K>>();
    
    // Graph radius.
    let rad = *ecc.iter().min_by(|x, y| x.partial_cmp(&y).unwrap()).unwrap();
    
    (0..graph.node_bound())
        .filter(|i| ecc[*i] == rad)
        .map(|i| graph.from_index(i))
        .collect()
}


/// Peripheral vertices of a weighted graph.
/// 
/// Calculate the peripheral vertices of the graph given the edge weights. 
/// The function is based on the [Floyd–Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm)
/// and has a time complexity of **O(|V|^3)**. 
/// So if edge weights is not important it is better to use `periphery()` function.
/// 
/// ## Arguments
/// * `graph`: weighted graph.
/// * `edge_cost`: closure that returns weight of a particular edge.
///
/// ## Returns
/// * A vector of indices of peripheral vertices.
/// * `vec![]`: if the graph contains a negative cycle.
/// 
/// ```
/// use graphalgs::metrics::weighted_periphery;
/// use petgraph::Graph;
/// 
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
///     (3, 2, 2.0), (2, 3, 20.0), (3, 0, 3.0),
/// ]);
/// 
/// assert_eq!(weighted_periphery(&graph, |edge| *edge.weight()), vec![2.into()]);
/// 
/// // Negative cycle.
/// let graph = Graph::<(), f32>::from_edges(&[
///     (0, 1, 2.0), (1, 2, 2.0), (2, 0, -10.0)
/// ]);
/// 
/// assert_eq!(weighted_periphery(&graph, |edge| *edge.weight()), vec![]);
/// ```
pub fn weighted_periphery<G, F, K>(graph: G, edge_cost: F) -> Vec<G::NodeId>
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure,
{
    if graph.node_count() == 0 {
        return vec![];
    }

    let distances = floyd_warshall(graph, edge_cost);

    if distances.is_err() {
        return vec![];  // The graph contains a negative cycle.
    }
    
    // Vector of node eccentricities.
    let ecc = distances.unwrap()
        .iter()
        .map(|dist| *dist.iter().max_by(|x, y| x.partial_cmp(&y).unwrap()).unwrap())
        .collect::<Vec<K>>();
    
    // Graph diameter.
    let diam = *ecc.iter().max_by(|x, y| x.partial_cmp(&y).unwrap()).unwrap();
    
    (0..graph.node_bound())
        .filter(|i| ecc[*i] == diam)
        .map(|i| graph.from_index(i))
        .collect()
}


#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::Graph;


    fn graph1() -> Graph<(), ()> {
        let mut graph = Graph::<(), ()>::new();
        let n0 = graph.add_node(()); let n1 = graph.add_node(());
        let n2 = graph.add_node(()); let n3 = graph.add_node(());
        let n4 = graph.add_node(()); let n5 = graph.add_node(());
        let n6 = graph.add_node(()); let n7 = graph.add_node(());
        let n8 = graph.add_node(()); let n9 = graph.add_node(());
        let n10 = graph.add_node(()); let n11 = graph.add_node(());

        graph.add_edge(n0, n1, ()); graph.add_edge(n0, n2, ());
        graph.add_edge(n2, n3, ()); graph.add_edge(n2, n5, ());
        graph.add_edge(n3, n4, ()); graph.add_edge(n4, n8, ());
        graph.add_edge(n5, n9, ()); graph.add_edge(n5, n6, ()); 
        graph.add_edge(n6, n3, ()); graph.add_edge(n6, n7, ());
        graph.add_edge(n6, n10, ()); graph.add_edge(n7, n8, ());
        graph.add_edge(n7, n11, ()); graph.add_edge(n8, n11, ()); 
        graph.add_edge(n9, n1, ()); graph.add_edge(n9, n10, ());
        graph.add_edge(n10, n6, ()); graph.add_edge(n11, n6, ()); 
        graph.add_edge(n11, n10, ()); graph.add_edge(n0, n9, ());

        graph
    }

    fn graph2() -> Graph<(), ()> {
        let mut graph = Graph::<(), ()>::new();
        let n0 = graph.add_node(()); let n1 = graph.add_node(());
        let n2 = graph.add_node(()); let n3 = graph.add_node(());
        let n4 = graph.add_node(()); let n5 = graph.add_node(());
        let n6 = graph.add_node(());

        graph.add_edge(n0, n6, ()); graph.add_edge(n0, n1, ());
        graph.add_edge(n1, n0, ()); graph.add_edge(n1, n2, ());
        graph.add_edge(n1, n5, ()); graph.add_edge(n1, n6, ());
        graph.add_edge(n2, n1, ()); graph.add_edge(n2, n3, ());
        graph.add_edge(n3, n2, ()); graph.add_edge(n3, n4, ());
        graph.add_edge(n4, n3, ()); graph.add_edge(n4, n5, ());
        graph.add_edge(n5, n2, ()); graph.add_edge(n5, n6, ());
        graph.add_edge(n5, n1, ()); graph.add_edge(n5, n4, ());
        graph.add_edge(n6, n0, ()); graph.add_edge(n6, n1, ());
        graph.add_edge(n6, n5, ()); graph.add_edge(n2, n5, ()); 

        graph
    }

    fn graph3() -> Graph<(), f32> {
        let mut graph = Graph::<(), f32>::new();
        graph.add_node(());
        graph
    }
    
    fn graph4() -> Graph<(), f32> { 
        Graph::<(), f32>::new() 
    }
    
    fn graph5() -> Graph<(), f32> {
        let mut graph = Graph::new();
        let n0 = graph.add_node(()); let n1 = graph.add_node(());
        let n2 = graph.add_node(()); let n3 = graph.add_node(());
        let n4 = graph.add_node(()); let n5 = graph.add_node(());

        graph.add_edge(n1, n0, 10.0); graph.add_edge(n1, n0, 10.0);
        graph.add_edge(n0, n3, 14.0); graph.add_edge(n3, n0, 14.0);
        graph.add_edge(n1, n2, 5.0); graph.add_edge(n2, n1, -5.0);
        graph.add_edge(n2, n3, 1.0);  graph.add_edge(n3, n2, 1.0); 
        graph.add_edge(n2, n4, 3.0);  graph.add_edge(n4, n2, 3.0);
        graph.add_edge(n3, n5, -1.0);

        graph
    }
    
    fn graph6() -> Graph<(), f32> {
        let mut graph = Graph::new();
        graph.add_node(()); graph.add_node(());

        graph
    }

    #[test]
    fn test_eccentricity() {
        let inf = f32::INFINITY;

        let g = graph1();
        assert_eq!(eccentricity(&g, 0.into()), 5.0);
        for i in 1..12 {
            assert_eq!(eccentricity(&g, i.into()), inf);
        }

        let g = graph2();
        assert_eq!(eccentricity(&g, 0.into()), 3.0);
        assert_eq!(eccentricity(&g, 1.into()), 2.0);
        assert_eq!(eccentricity(&g, 2.into()), 2.0);
        assert_eq!(eccentricity(&g, 3.into()), 3.0);
        assert_eq!(eccentricity(&g, 4.into()), 3.0);
        assert_eq!(eccentricity(&g, 5.into()), 2.0);
        assert_eq!(eccentricity(&g, 6.into()), 3.0);

        let g = graph3();
        assert_eq!(eccentricity(&g, 0.into()), 0.0);
    }
    
    #[test]
    fn test_radius() {
        let inf = f32::INFINITY;
        
        assert_eq!(radius(&graph1()), Some(5.0));
        assert_eq!(radius(&graph2()), Some(2.0));
        assert_eq!(radius(&graph3()), Some(0.0));
        assert_eq!(radius(&graph4()), None);
        assert_eq!(radius(&graph5()), Some(2.0));
        assert_eq!(radius(&graph6()), Some(inf));
    }
    
    #[test]
    fn test_diameter() {
        let inf = f32::INFINITY;
        
        assert_eq!(diameter(&graph1()), Some(inf));
        assert_eq!(diameter(&graph2()), Some(3.0));
        assert_eq!(diameter(&graph3()), Some(0.0));
        assert_eq!(diameter(&graph4()), None);
        assert_eq!(diameter(&graph5()), Some(inf));
        assert_eq!(diameter(&graph6()), Some(inf));
    }
    
    #[test]
    fn test_center() {
        assert_eq!(center(&graph1()), vec![0.into()]);
        assert_eq!(center(&graph2()), vec![1.into(), 2.into(), 5.into()]);
        assert_eq!(center(&graph3()), vec![0.into()]);
        assert_eq!(center(&graph4()), vec![]);
        assert_eq!(center(&graph5()), vec![2.into(), 3.into()]);
        assert_eq!(center(&graph6()), vec![0.into(), 1.into()]);
    }
    
    #[test]
    fn test_periphery() {
        assert_eq!(
            periphery(&graph1()), 
            vec![1.into(), 2.into(), 3.into(), 4.into(), 5.into(), 
                 6.into(), 7.into(), 8.into(), 9.into(), 10.into(), 11.into()]
        );
        assert_eq!(periphery(&graph2()), vec![0.into(), 3.into(), 4.into(), 6.into()]);
        assert_eq!(periphery(&graph3()), vec![0.into()]);
        assert_eq!(periphery(&graph4()), vec![]);
        assert_eq!(periphery(&graph5()), vec![5.into()]);
        assert_eq!(periphery(&graph6()), vec![0.into(), 1.into()]);
    }
    
    #[test]
    fn test_weighted_eccentricity() {
        let inf = f32::INFINITY;

        let g = graph3();
        assert_eq!(weighted_eccentricity(&g, 0.into()), Some(0.0));
        
        let graph = graph5();
        assert_eq!(weighted_eccentricity(&graph, 0.into()), Some(18.0));
        assert_eq!(weighted_eccentricity(&graph, 1.into()), Some(10.0));
        assert_eq!(weighted_eccentricity(&graph, 2.into()), Some(5.0));
        assert_eq!(weighted_eccentricity(&graph, 3.into()), Some(6.0));
        assert_eq!(weighted_eccentricity(&graph, 4.into()), Some(8.0));
        assert_eq!(weighted_eccentricity(&graph, 5.into()), Some(inf));
    }
    
    #[test]
    fn test_weighted_radius() {
        let inf = f32::INFINITY;
        
        assert_eq!(weighted_radius(&graph1(), |_| 1.0), Some(5.0));
        assert_eq!(weighted_radius(&graph2(), |_| 2.0), Some(4.0));
        assert_eq!(weighted_radius(&graph3(), |edge| *edge.weight()), Some(0.0));
        assert_eq!(weighted_radius(&graph4(), |edge| *edge.weight()), None);
        assert_eq!(weighted_radius(&graph5(), |edge| *edge.weight()), Some(5.0));
        assert_eq!(weighted_radius(&graph6(), |edge| *edge.weight()), Some(inf));
    }
    
    #[test]
    fn test_weighted_diameter() {
        let inf = f32::INFINITY;
        
        assert_eq!(weighted_diameter(&graph1(), |_| 1.0), Some(inf));
        assert_eq!(weighted_diameter(&graph2(), |_| 2.0), Some(6.0));
        assert_eq!(weighted_diameter(&graph3(), |edge| *edge.weight()), Some(0.0));
        assert_eq!(weighted_diameter(&graph4(), |edge| *edge.weight()), None);
        assert_eq!(weighted_diameter(&graph5(), |edge| *edge.weight()), Some(inf));
        assert_eq!(weighted_diameter(&graph6(), |edge| *edge.weight()), Some(inf));
    }
    
    #[test]
    fn test_weighted_center() {
        assert_eq!(weighted_center(&graph1(), |_| 1.0), vec![0.into()]);
        assert_eq!(weighted_center(&graph2(), |_| 2.0), vec![1.into(), 2.into(), 5.into()]);
        assert_eq!(weighted_center(&graph3(), |edge| *edge.weight()), vec![0.into()]);
        assert_eq!(weighted_center(&graph4(), |edge| *edge.weight()), vec![]);
        assert_eq!(weighted_center(&graph5(), |edge| *edge.weight()), vec![2.into()]);
        assert_eq!(weighted_center(&graph6(), |edge| *edge.weight()), vec![0.into(), 1.into()]);
    }
    
    #[test]
    fn test_weighted_periphery() {
        assert_eq!(
            weighted_periphery(&graph1(), |_| 1.0), 
            vec![1.into(), 2.into(), 3.into(), 4.into(), 5.into(), 
                 6.into(), 7.into(), 8.into(), 9.into(), 10.into(), 11.into()]
        );
        assert_eq!(weighted_periphery(&graph2(), |_| 2.0), vec![0.into(), 3.into(), 4.into(), 6.into()]);
        assert_eq!(weighted_periphery(&graph3(), |edge| *edge.weight()), vec![0.into()]);
        assert_eq!(weighted_periphery(&graph4(), |edge| *edge.weight()), vec![]);
        assert_eq!(weighted_periphery(&graph5(), |edge| *edge.weight()), vec![5.into()]);
        assert_eq!(weighted_periphery(&graph6(), |edge| *edge.weight()), vec![0.into(), 1.into()]);
    }
}
