//! Minimum spanning tree (MST) algorithms.
//!
//! The `kruskal` function is a reimported `min_spanning_tree` function from the 'petgraph' crate.

pub use petgraph::algo::min_spanning_tree as kruskal;
mod prim;
pub use prim::prim;
mod boruvka;
pub use boruvka::boruvka;
