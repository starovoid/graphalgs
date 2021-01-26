# graphalgs

* [Documentation](https://docs.rs/graphalgs/)
* [Crate](https://crates.io/crates/graphalgs)


## Description

<p>Graph algorithms based on the Rust "petgraph" library.</p>

## Relevance

```petgraph``` is a great tool for working with graphs in ```Rust```, but not all algorithms make sense to put there, so the ```graphalgs``` library will be a repository for a variety of algorithms implemented on the basis of ```petgraph```.</p>

## Stage of development

<p>This is a pre-alpha stage of development, published mainly to take a name on crates.io. All code changes will occur on github without updating the crate until the product is ready to release the alpha version.</p>

## Usage

As a library
```rust
extern crate graphalgs;

```

## Upcoming plans

In the near future, we plan to implement such graph metrics as the eccentricity of an arbitrary vertex, radius and diameter, as well as finding the center and periphery of the graph, + versions of these algorithms that take into account the weights of edges and vertices. After that, the project will be compiled and released on crates.io under version 0.0.3.

If you have any comments or suggestions, or you suddenly found an error, please write to prototyperailgun@gmail.com.
