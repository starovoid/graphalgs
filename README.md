# graphalgs

* [Documentation](https://docs.rs/graphalgs/)
* [Crate](https://crates.io/crates/graphalgs)


## Description

Graph algorithms based on the Rust "petgraph" library.


## Relevance

```petgraph``` is a great tool for working with graphs in ```Rust```, but not all algorithms make sense to put there, so the ```graphalgs``` library will be a repository for a variety of algorithms implemented on the basis of ```petgraph```.


## What's new

1. Added a function that calculates the complement of the input graph.
2. Added algorithms for finding bridges and articulation points of a simple undirected graph.
3. The connectivity algorithms are grouped into separate module.
4. Added the "girth" metric for a simple unweighted graph.

## Usage

As a library
```rust
extern crate graphalgs;

```

If you have any comments or suggestions, or you suddenly found an error, please start a new issue or pool request.
