//! Shortest path algorithms.
//!
//! Functions `dijkstra`, `bellman_ford` and `astar` are taken from the 'petgraph' crate.

mod shortest_distances;
pub use shortest_distances::shortest_distances;

mod floyd_warshall;
pub use floyd_warshall::{distance_map, floyd_warshall, NegativeCycle};

mod spfa;
pub use spfa::spfa;

mod johnson;
pub use johnson::johnson;

mod seidel;
pub use seidel::{apd, seidel};

pub use petgraph::algo::floyd_warshall::floyd_warshall as floyd_warshall_petgraph;
pub use petgraph::algo::{astar, bellman_ford, dijkstra};
