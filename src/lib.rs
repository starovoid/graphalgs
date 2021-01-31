#[doc(no_inline)]
extern crate petgraph;
#[doc(no_inline)]
extern crate nalgebra;

pub mod adj_matrix;
pub mod spec;

mod shortest_distances;
pub use shortest_distances::shortest_distances;

mod floyd_warshall;
pub use floyd_warshall::{ floyd_warshall, NegativeCycle };

pub mod metrics;
