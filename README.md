# graphalgs

* [Documentation](https://docs.rs/graphalgs/)
* [Crate](https://crates.io/crates/graphalgs)


## Description

Graph algorithms based on the Rust "petgraph" library.


## Relevance

```petgraph``` is a great tool for working with graphs in ```Rust```, but not all algorithms make sense to put there, so the ```graphalgs``` library will be a repository for a variety of algorithms implemented on the basis of ```petgraph```.


## What's new

1. A critical change in version 0.0.4 was the regrouping of the shortest path algorithms into a separate module 'shortest_path'. 
2. Algorithms for generating random directed graphs (simple and weighted versions) were added.
3. Algorithms were added to simplify the work with tournaments:
    * Is the graph a tournament?
    * Is a tournament transitive?
    * Generation of a random tournament with a given number of vertices.
4. Added random tests for shortest_distances() and floyd_warshall().

## Usage

As a library
```rust
extern crate graphalgs;

```

If you have any comments or suggestions, or you suddenly found an error, please write to prototyperailgun@gmail.com or start  a new issue or pool request.
