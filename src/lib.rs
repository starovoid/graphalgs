//! `graphalgs` is a graph algorithms library based on the Rust
//! [petgraph](https://docs.rs/petgraph/0.5.1/petgraph/) crate.
//!
//! # Examples
//!
//! ```
//! use graphalgs::shortest_path::floyd_warshall;
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
pub extern crate nalgebra;
#[doc(no_inline)]
pub extern crate petgraph;

pub mod adj_matrix;
pub mod connect;
pub mod elementary;
pub mod generate;
pub mod metrics;
pub mod mst;
pub mod shortest_path;
pub mod spec;
pub mod tournament;
pub mod traits;
