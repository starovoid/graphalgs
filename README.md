# graphalgs

* [Documentation](https://docs.rs/graphalgs/)
* [Crate](https://crates.io/crates/graphalgs)


## Description

Graph algorithms based on the Rust "petgraph" library.


## Relevance

```petgraph``` is a great tool for working with graphs in ```Rust```, but not all algorithms make sense to put there, so the ```graphalgs``` library will be a repository for a variety of algorithms implemented on the basis of ```petgraph```.


## What's new

1. Algorithms for generating random undirected graphs (weighted and unweighted versions) were added.
2. The following algorithms for solving the shortest path problems have been implemented:
    * SPFA
    * Johnson's algorithm
    * Seidel'a algorithm
3. Nalgebra updated to version "0.25.1".

## Usage

As a library
```rust
extern crate graphalgs;

```

If you have any comments or suggestions, or you suddenly found an error, please start a new issue or pool request.
