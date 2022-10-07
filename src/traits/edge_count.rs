//! Graph with known number of edges.

use petgraph::csr::Csr;
use petgraph::graph::{Graph, IndexType};
use petgraph::graphmap::{GraphMap, NodeTrait};
use petgraph::matrix_graph::MatrixGraph;
use petgraph::stable_graph::StableGraph;
use petgraph::EdgeType;

pub trait EdgeCount {
    fn number_of_edges(self) -> usize;
}

impl<'a, N: 'a, E: 'a, Ty: EdgeType, Ix: IndexType> EdgeCount for &'a Graph<N, E, Ty, Ix> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<N, E, Ty: EdgeType, Ix: IndexType> EdgeCount for Graph<N, E, Ty, Ix> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a, E: 'a, Ty: EdgeType, Ix: IndexType> EdgeCount for &'a StableGraph<N, E, Ty, Ix> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<N, E, Ty: EdgeType, Ix: IndexType> EdgeCount for StableGraph<N, E, Ty, Ix> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a + NodeTrait, E: 'a, Ty: EdgeType> EdgeCount for &'a GraphMap<N, E, Ty> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<N: NodeTrait, E, Ty: EdgeType> EdgeCount for GraphMap<N, E, Ty> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a, E: 'a, Ty: EdgeType> EdgeCount for &'a MatrixGraph<N, E, Ty> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<N, E, Ty: EdgeType> EdgeCount for MatrixGraph<N, E, Ty> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<'a, N: 'a, E: 'a, Ty: EdgeType> EdgeCount for &'a Csr<N, E, Ty> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}

impl<N, E, Ty: EdgeType> EdgeCount for Csr<N, E, Ty> {
    fn number_of_edges(self) -> usize {
        self.edge_count()
    }
}
