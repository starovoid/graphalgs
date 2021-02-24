//! Graph generators.

use std::collections::{ HashSet, HashMap };
use rand::Rng;
use rand::distributions::uniform::SampleUniform;
use petgraph::algo::FloatMeasure;


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
/// use graphalgs::generate::random_digraph;
/// use petgraph::{ Graph, Directed };
/// 
/// let graph: Graph::<(), (), Directed, usize> = Graph::from_edges(
///     random_digraph(4, 11).unwrap()
/// );
/// ```
pub fn random_digraph(
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


/// Random directed weighted graph.
/// 
/// Create and return a random graph with a specified number of vertices and edges 
/// and random edge weights from a given range `[min_w, max_w)`.
/// Note: weights must have the [FloatMeasure](https://docs.rs/petgraph/0.5.1/petgraph/algo/trait.FloatMeasure.html) 
/// + [SampleUniform](https://docs.rs/rand/0.8.3/rand/distributions/uniform/trait.SampleUniform.html) trait.
/// 
/// ## Arguments
/// * `nodes`: number of nodes.
/// * `nedges`: number of edges.
/// * `min_w`: lower bound of possible weights.
/// * `max_w`: upper bound of possible weights.
///
/// ## Returns
/// * `Err`: if the required number of vertices is greater than the maximum possible.
/// * `Ok`: set `HashMap<(usize, usize), K>` of edges with `usize` vertex indices, 
///         where `K: FloatMeasure + SampleUniform`.
/// 
/// # Examples
/// 
/// ```
/// use graphalgs::generate::random_weighted_digraph;
/// use petgraph::{ Graph, Directed };
/// 
/// let graph: Graph::<(), f64, Directed, usize> = Graph::from_edges(
///     random_weighted_digraph(5, 16, -10.0, 10.0)
///     .unwrap().into_iter().map(|(edge, w)| (edge.0, edge.1, w))
/// );
/// ```
pub fn random_weighted_digraph<K: FloatMeasure + SampleUniform>(
        nodes: usize, nedges: usize, min_w: K, max_w: K) -> Result<HashMap<(usize, usize), K>, EdgeNumberError> {

    if nodes == 0 {
        return Ok(HashMap::new())
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
    let mut edges = HashMap::with_capacity(nedges);
    let mut count = 0;

    while count < nedges {
        let i = rng.gen_range(0..nodes);
        let j = rng.gen_range(0..nodes);

        if i != j && !edges.contains_key(&(i, j)) {
            edges.insert((i, j), rng.gen_range(min_w..max_w));
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
    fn test_random_digraph() {
        assert!(random_digraph(5, 10).is_ok());
        assert!(random_digraph(0, 0).is_ok());
        assert!(random_digraph(50, 1000).is_ok());
        assert_eq!(
            random_digraph(5, 100),
            Err(EdgeNumberError {
                    nodes: 5,
                    nedges: 100,
                    max_edges: 20,
                }
            )
        );
        println!("{:?}", &Graph::<(), (), Directed, usize>::from_edges(random_digraph(4, 11).unwrap()));
    }

    #[test]
    fn test_random_weighted_digraph() {
        assert!(random_weighted_digraph(5, 10, -100f32, 100f32).is_ok());
        assert!(random_weighted_digraph(0, 0, -100f64, 100f64).is_ok());
        assert!(random_weighted_digraph(50, 1000, 0.0, 0.001).is_ok());
        assert_eq!(
            random_weighted_digraph(5, 100, -10.0, 10.0),
            Err(EdgeNumberError {
                    nodes: 5,
                    nedges: 100,
                    max_edges: 20,
                }
            )
        );
        println!("{:?}", &Graph::<(), f32, Directed, usize>::from_edges(
            random_weighted_digraph(4, 11, -10.0, 10.0).unwrap().into_iter().map(|(edge, w)| (edge.0, edge.1, w))
        ));
    }
}
