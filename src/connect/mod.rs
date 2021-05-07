//! Algorithms related to [graph connectivity](https://en.wikipedia.org/wiki/Connectivity_(graph_theory)).

pub use petgraph::algo::{ connected_components, has_path_connecting };

pub mod scc {
    //! [Strongly connected components](https://en.wikipedia.org/wiki/Strongly_connected_component) algorithms.
    //! Functions `condensation`, `kosaraju_scc` and `tarjan_scc` are taken from the 'petgraph' crate.
    pub use petgraph::algo::{
        condensation, kosaraju_scc,  tarjan_scc,
    };
}
