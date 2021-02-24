//! Shortest path algorithms.
//! 
//! Functions `dijkstra`, `bellman_ford` and `astar` are taken from the 'petgraph' crate.

mod shortest_distances;
pub use shortest_distances::shortest_distances;

mod floyd_warshall;
pub use floyd_warshall::{ floyd_warshall, distance_map, NegativeCycle };

pub use petgraph::algo::{ dijkstra, bellman_ford, astar };
