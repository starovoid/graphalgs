//! `graphalgs` is a graph algorithms library based on the Rust 'petgraph' crate.
//! 
//! # Examples
//! 
//! ```
//! use graphalgs::floyd_warshall;
//! use graphalgs::metrics::{ weighted_radius, weighted_diameter };
//! use petgraph::Graph;
//! 
//! let inf = f32::INFINITY;
//! 
//! // Create a graph with `f32` edge weights.
//! let graph = Graph::<(), f32>::from_edges(&[
//!     (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
//!     (3, 2, 2.0), (2, 3, 20.0),
//! ]);
//! 
//! // Calculate the distance matrix using the Floyd-Warshall algorithm.
//! assert_eq!(
//!     floyd_warshall(&graph, |edge| *edge.weight()),
//!     Ok(vec![vec![0.0, 2.0, -1.0, -3.0],
//!             vec![inf, 0.0, -3.0, -5.0],
//!             vec![inf, inf,  0.0, 20.0],
//!             vec![inf, inf,  2.0,  0.0]])
//! );
//! 
//! // Calculate the radius and diameter of this graph, 
//! // taking into account the weights of the edges.
//! assert_eq!(weighted_radius(&graph, |edge| *edge.weight()), Some(2.0));
//! assert_eq!(weighted_diameter(&graph, |edge| *edge.weight()), Some(inf));
//! ```

#[doc(no_inline)]
pub extern crate petgraph;
#[doc(no_inline)]
pub extern crate nalgebra;

pub mod adj_matrix;
pub mod spec;

mod shortest_distances;
pub use shortest_distances::shortest_distances;

mod floyd_warshall;
pub use floyd_warshall::{ floyd_warshall, NegativeCycle, distance_map };

pub mod metrics;
