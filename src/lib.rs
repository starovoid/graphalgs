#[doc(no_inline)]
extern crate petgraph;
#[doc(no_inline)]
extern crate nalgebra;

pub mod adj_matrix;
pub mod spec;

pub mod shortest_distances;
pub use shortest_distances::shortest_distances;
