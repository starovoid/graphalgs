# graphalgs

* [Documentation](https://docs.rs/graphalgs/)
* [Crate](https://crates.io/crates/graphalgs)


# Description

Graph algorithms based on the Rust "petgraph" library.

# Relevance

```Petgraph``` is a great tool for working with graphs in ```Rust```, but not all algorithms make sense to put there, so the ```graphalgs``` library will be a repository for a variety of algorithms implemented on the basis of ```petgraph```.

# Main features
## Shortest path algorithms
1. [APD](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.apd.html) ([Seidel](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.seidel.html)) algorithm for all pairs shortest path problem in **unweighted**, **undirected**, **connected graph**. This algorithm shows remarkable performance due to the use of matrix multiplication.
2. [A*](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.astar.html) shortest path algorithm re-exported from petgraph.
3. [Bellman-Ford](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.bellman_ford.html) algorithm for computing shortest paths from *source* node to all other re-exported from petgraph.
4. [Dijkstra’s](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.dijkstra.html#) shortest path algorithm re-exported from petgraph.
5. [Floyd–Warshall](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.floyd_warshall.html) algorithm for all pairs shortest path problem.
6. [Johnson](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.johnson.html) algorithm for all pairs shortest path problem.
7. [Shortest Path Faster Algorithm](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.spfa.html) Compute shortest distances from source node to all other.
8. [shortest_distances](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.shortest_distances.html) algorithm based on BFS.
9. [distance_map](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.distance_map.html) Convert distance matrix into hashmap.
10. [Floyd–Warshall from petgraph](https://docs.rs/graphalgs/latest/graphalgs/shortest_path/fn.floyd_warshall_petgraph.html)
11. [k'th shortest path algorithm](https://docs.rs/petgraph/latest/petgraph/algo/k_shortest_path/fn.k_shortest_path.html) Compute the length of the k'th shortest path from `start` to every reachable node. Re-exported from petgraph.

## Minimum spanning tree (MST) algorithms
1. [Borůvka’s algorithm](https://docs.rs/graphalgs/latest/graphalgs/mst/fn.boruvka.html)
2. [Prim’s algorithm](https://docs.rs/graphalgs/latest/graphalgs/mst/fn.prim.html)
3. [Kruskal’s algorithm](https://docs.rs/graphalgs/latest/graphalgs/mst/fn.kruskal.html) re-exported from petgraph.

## Metrics
Basic graph characteristics based on the concept of distance between vertices.

1. [Center](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.center.html) and its [weighted](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.weighted_center.html) version.
2. [Diametr](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.diameter.html) and its [weighted](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.weighted_diameter.html) version.
3. [Radius](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.radius.html) and its [weighted](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.weighted_radius.html) version.
4. [Eccentricity of node](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.eccentricity.html) and its [weighted](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.weighted_eccentricity.html) version.
5. [Peripheral graph vertices](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.periphery.html) and its [weighted](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.weighted_eccentricity.html) version.
6. [Girth](https://docs.rs/graphalgs/latest/graphalgs/metrics/fn.girth.html)

## Algorithms related to graph connectivity
1. [Articulation points](https://docs.rs/graphalgs/latest/graphalgs/connect/fn.articulation_points.html)
2. [Bridges](https://docs.rs/graphalgs/latest/graphalgs/connect/fn.find_bridges.html)
3. [Number of connected components](https://docs.rs/graphalgs/latest/graphalgs/connect/fn.connected_components.html) re-exported from petgraph.
4. [Has path connecting](https://docs.rs/graphalgs/latest/graphalgs/connect/fn.has_path_connecting.html) re-exported from petgraph.
5. [Condensation](https://docs.rs/graphalgs/latest/graphalgs/connect/scc/fn.condensation.html) Condense every strongly connected component into a single node and return the result (re-exported from petgraph).
6. [Kosaraju’s algorithm](https://docs.rs/graphalgs/latest/graphalgs/connect/scc/fn.kosaraju_scc.html) (re-exported from petgraph).
7. [Tarjan’s algorithm](https://docs.rs/graphalgs/latest/graphalgs/connect/scc/fn.tarjan_scc.html) (re-exported from petgraph).

## Generate
Generating various graphs.

1. [Complement](https://docs.rs/graphalgs/latest/graphalgs/generate/fn.complement.html)
2. [Random directed graph](https://docs.rs/graphalgs/latest/graphalgs/generate/fn.random_digraph.html)
3. [Random directed weighted graph](https://docs.rs/graphalgs/latest/graphalgs/generate/fn.random_weighted_digraph.html)
4. [Random undirected graph](https://docs.rs/graphalgs/latest/graphalgs/generate/fn.random_ungraph.html)
5. [Random undirected weighted graph](https://docs.rs/graphalgs/latest/graphalgs/generate/fn.random_weighted_ungraph.html)

## Tournament
Algorithms that simplify work with such type of graphs as a 
[tournament](https://en.wikipedia.org/wiki/Tournament_(graph_theory)).

1. [Is the graph a tournament?](https://docs.rs/graphalgs/latest/graphalgs/tournament/fn.is_tournament.html)
2. [Is the tournament transitive?](https://docs.rs/graphalgs/latest/graphalgs/tournament/fn.is_tournament_transitive.html)
3. [Generate random tournament](https://docs.rs/graphalgs/latest/graphalgs/tournament/fn.random_tournament.html)

## Special algorithms that are difficult to categorize
1. [Check whether the sequence of numbers is graph-like](https://docs.rs/graphalgs/latest/graphalgs/spec/fn.is_degree_sequence_graphlike.html)
2. [Prufer encode](https://docs.rs/graphalgs/latest/graphalgs/spec/fn.prufer_code.html)
3. [Prufer decode](https://docs.rs/graphalgs/latest/graphalgs/spec/fn.prufer_decode.html)
4. [Counting spanning trees](https://docs.rs/graphalgs/latest/graphalgs/spec/fn.count_spanning_trees.html)
5. [Laplacian matrix](https://docs.rs/graphalgs/latest/graphalgs/spec/fn.laplacian_matrix.html)

## Circuits
1. [Elementary circuits](https://docs.rs/graphalgs/latest/graphalgs/elementary_circuits/fn.elementary_circuits.html)

# Usage

As a library
```rust
use graphalgs::shortest_path::floyd_warshall;
use graphalgs::metrics::{ weighted_radius, weighted_diameter };
use petgraph::Graph;

let inf = f32::INFINITY;

// Create a graph with `f32` edge weights.
let graph = Graph::<(), f32>::from_edges(&[
    (0, 1, 2.0), (1, 2, 10.0), (1, 3, -5.0), 
    (3, 2, 2.0), (2, 3, 20.0),
]);

// Calculate the distance matrix using the Floyd-Warshall algorithm.
assert_eq!(
    floyd_warshall(&graph, |edge| *edge.weight()),
    Ok(vec![vec![0.0, 2.0, -1.0, -3.0],
            vec![inf, 0.0, -3.0, -5.0],
            vec![inf, inf,  0.0, 20.0],
            vec![inf, inf,  2.0,  0.0]])
);

// Calculate the radius and diameter of this graph, 
// taking into account the weights of the edges.
assert_eq!(weighted_radius(&graph, |edge| *edge.weight()), Some(2.0));
assert_eq!(weighted_diameter(&graph, |edge| *edge.weight()), Some(inf));
```

If you have any comments or suggestions, or you suddenly found an error, please start a new issue or pool request.
