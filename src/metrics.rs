use crate::shortest_distances;
use petgraph::visit::{ Visitable, NodeIndexable, IntoEdges, IntoNeighbors };

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

    fn graph3() -> Graph<(), ()> {
        let mut graph = Graph::<(), ()>::new();
        graph.add_node(());
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
}