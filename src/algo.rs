use std::collections::VecDeque;
use petgraph::visit::{ Visitable, VisitMap, NodeIndexable, IntoEdges };


/// The lengths of the shortest paths from the start vertex to all the others.
/// 
/// The algorithm is based on BFS, and the path length is equal to the number of edges in this path.
/// If it is impossible to get from the vertex x to the vertex y, then the distance from x to y will be equal to f32::INFINITY.
/// Time complexity: **O(|V| + |E|)**, where **|V|** is the number of vertices, and **|E|** is the number of edges in the graph.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::algo::shortest_distances;
/// use petgraph::Graph;
/// 
/// let inf = f32::INFINITY;
/// let graph = Graph::<u8, ()>::from_edges(&[(0, 1), (0, 2), (1, 2)]);
/// 
/// assert_eq!(shortest_distances(&graph, 0.into()), vec![0.0, 1.0, 1.0]);
/// assert_eq!(shortest_distances(&graph, 1.into()), vec![inf, 0.0, 1.0]);
/// assert_eq!(shortest_distances(&graph, 2.into()), vec![inf, inf, 0.0]);
/// ```
pub fn shortest_distances<G>(graph: G, start: G::NodeId) -> Vec<f32> 
where 
    G: Visitable + NodeIndexable + IntoEdges
{
    let mut visit_map = graph.visit_map();
    visit_map.visit(start);

    let mut dist = vec![f32::INFINITY; graph.node_bound()];
    dist[graph.to_index(start)] = 0.0;

    let mut queue: VecDeque<G::NodeId> = VecDeque::new();
    queue.push_back(start);
    
    while queue.len() != 0 {
        let current = queue.pop_front().unwrap();
        for v in graph.neighbors(current) {
            if visit_map.visit(v) {
                queue.push_back(v);
                dist[graph.to_index(v)] = dist[graph.to_index(current)] + 1.0;
            }
        }
    }

    dist
}


#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::Graph;

    #[test]
    fn test_shortest_distances() {
        let inf = f32::INFINITY;
        
        let graph = Graph::<u8, ()>::from_edges(&[
            (0, 1), (0, 2), (2, 3), (2, 5), (3, 4), (4, 8), (5, 9), 
            (5, 6), (6, 3), (6, 7), (6, 10), (7, 8), (7, 11), (8, 11), 
            (9, 1), (9, 10), (10, 6), (11, 6), (11, 10),
        ]);

        assert_eq!(shortest_distances(&graph, graph.from_index(0)), 
                   vec![0.0, 1.0, 1.0, 2.0, 3.0, 2.0, 3.0, 4.0, 4.0, 3.0, 4.0, 5.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(1)), 
                   vec![inf, 0.0, inf, inf, inf, inf, inf, inf, inf, inf, inf, inf]);
        assert_eq!(shortest_distances(&graph, graph.from_index(2)), 
                   vec![inf, 3.0, 0.0, 1.0, 2.0, 1.0, 2.0, 3.0, 3.0, 2.0, 3.0, 4.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(3)), 
                   vec![inf, inf, inf, 0.0, 1.0, inf, 4.0, 5.0, 2.0, inf, 4.0, 3.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(4)), 
                   vec![inf, inf, inf, 4.0, 0.0, inf, 3.0, 4.0, 1.0, inf, 3.0, 2.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(5)), 
                   vec![inf, 2.0, inf, 2.0, 3.0, 0.0, 1.0, 2.0, 3.0, 1.0, 2.0, 3.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(6)), 
                   vec![inf, inf, inf, 1.0, 2.0, inf, 0.0, 1.0, 2.0, inf, 1.0, 2.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(7)), 
                   vec![inf, inf, inf, 3.0, 4.0, inf, 2.0, 0.0, 1.0, inf, 2.0, 1.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(8)), 
                   vec![inf, inf, inf, 3.0, 4.0, inf, 2.0, 3.0, 0.0, inf, 2.0, 1.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(9)), 
                   vec![inf, 1.0, inf, 3.0, 4.0, inf, 2.0, 3.0, 4.0, 0.0, 1.0, 4.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(10)), 
                   vec![inf, inf, inf, 2.0, 3.0, inf, 1.0, 2.0, 3.0, inf, 0.0, 3.0]);
        assert_eq!(shortest_distances(&graph, graph.from_index(11)), 
                   vec![inf, inf, inf, 2.0, 3.0, inf, 1.0, 2.0, 3.0, inf, 1.0, 0.0]);

    let graph = Graph::<u8, ()>::from_edges(&[
        (0, 1), (0, 6), (1, 0), (1, 2), (1, 5), (1, 6), (2, 1), 
        (2, 3), (2, 5), (3, 2), (3, 4), (4, 3), (4, 5), (5, 2), 
        (5, 6), (5, 1), (5, 4), (6, 0), (6, 1), (6, 5),
    ]);

    assert_eq!(shortest_distances(&graph, graph.from_index(0)), vec![0.0, 1.0, 2.0, 3.0, 3.0, 2.0, 1.0]);
    assert_eq!(shortest_distances(&graph, graph.from_index(1)), vec![1.0, 0.0, 1.0, 2.0, 2.0, 1.0, 1.0]);
    assert_eq!(shortest_distances(&graph, graph.from_index(2)), vec![2.0, 1.0, 0.0, 1.0, 2.0, 1.0, 2.0]);
    assert_eq!(shortest_distances(&graph, graph.from_index(3)), vec![3.0, 2.0, 1.0, 0.0, 1.0, 2.0, 3.0]);
    assert_eq!(shortest_distances(&graph, graph.from_index(4)), vec![3.0, 2.0, 2.0, 1.0, 0.0, 1.0, 2.0]);
    assert_eq!(shortest_distances(&graph, graph.from_index(5)), vec![2.0, 1.0, 1.0, 2.0, 1.0, 0.0, 1.0]);
    assert_eq!(shortest_distances(&graph, graph.from_index(6)), vec![1.0, 1.0, 2.0, 3.0, 2.0, 1.0, 0.0]);
    }
}
