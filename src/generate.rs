//! Graph generators.

use std::collections::HashSet;
use rand::Rng;


/// Graph generation error: more edges are specified 
/// than is possible for a given number of vertices.
#[derive(Clone, Debug, PartialEq)]
pub struct EdgeNumberError {
    pub nodes: usize,
    pub nedges: usize,
    pub max_edges: usize,
}


/// Random directed graph.
/// 
/// Create and return a random directed graph with a given number of nodes and edges.
/// 
/// ## Arguments
/// * `nodes`: number of nodes.
/// * `nedges`: number of edges.
///
/// ## Returns
/// * `Err`: if the required number of vertices is greater than the maximum possible.
/// * `Ok`: set `HashSet<(usize, usize)>` of edges with `usize` vertex indices.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::generate::random_directed_graph;
/// use petgraph::{ Graph, Directed };
/// 
/// let graph: Graph::<(), (), Directed, usize> = Graph::from_edges(
///     random_directed_graph(4, 11).unwrap()
/// );
/// ```
pub fn random_directed_graph(
        nodes: usize, nedges: usize) -> Result<HashSet<(usize, usize)>, EdgeNumberError> {

    if nodes == 0 {
        return Ok(HashSet::new())
    }
    
    if nedges > nodes*(nodes-1) {
        return Err(
            EdgeNumberError { 
                nodes: nodes, 
                nedges: nedges, 
                max_edges: nodes*(nodes-1)
            }
        )
    }
    
    let mut rng = rand::thread_rng();
    let mut edges = HashSet::with_capacity(nedges);
    let mut count = 0;

    while count < nedges {
        let i = rng.gen_range(0..nodes);
        let j = rng.gen_range(0..nodes);

        if i != j && !edges.contains(&(i, j)) {
            edges.insert((i, j));
            count += 1;
        }
    }

    Ok(edges)
}


#[cfg(test)]
mod test {
    use super::*;
    use petgraph::Graph;
    use petgraph::Directed;
    
    #[test]
    fn test_random_directed_graph() {
        assert!(random_directed_graph(5, 10).is_ok());
        assert!(random_directed_graph(0, 0).is_ok());
        assert!(random_directed_graph(50, 1000).is_ok());
        assert_eq!(
            random_directed_graph(5, 100),
            Err(EdgeNumberError {
                    nodes: 5,
                    nedges: 100,
                    max_edges: 20,
                }
            )
        );

        println!("{:?}", &Graph::<(), (), Directed, usize>::from_edges(random_directed_graph(4, 11).unwrap()));
    }
}
