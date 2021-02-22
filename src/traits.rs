//! Some useful traits missing in petgraph.

use petgraph::{ Graph, EdgeType };
use petgraph::stable_graph::StableGraph;
use petgraph::graphmap::{ GraphMap, NodeTrait };
use petgraph::matrix_graph::MatrixGraph;
use petgraph::csr::Csr;


/// Graph with known number of edges.
pub trait EdgeCount {
    fn number_of_edges(&self) -> usize;
}


impl<'a, N: 'a, E: 'a> EdgeCount for &'a Graph<N, E> {
    fn number_of_edges(&self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a, E: 'a>  EdgeCount for &'a StableGraph<N, E> {
    fn number_of_edges(&self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a + NodeTrait, E: 'a, Ty: 'a + EdgeType> EdgeCount for &'a GraphMap<N, E, Ty> {
    fn number_of_edges(&self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a, E: 'a>  EdgeCount for &'a MatrixGraph<N, E> {
    fn number_of_edges(&self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a, E: 'a>  EdgeCount for &'a Csr<N, E> {
    fn number_of_edges(&self) -> usize {
        self.edge_count()
    }
}
