//! Finding all elementary circuits.
use petgraph::graph::IndexType;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Directed;
use petgraph::Graph;

enum Task {
    Search(usize),
    Unblock(usize),
}

fn elementary_circuits_starting_at_s<Ix>(
    perfgraph: &Vec<Vec<usize>>,
    is_precessor_of_s: &[bool],
    circuits: &mut Vec<Vec<NodeIndex<Ix>>>,
    s: usize,
) where
    Ix: IndexType,
{
    let mut path = Vec::<NodeIndex<Ix>>::new();
    let mut blocked = vec![false; perfgraph.len()];
    let mut tasks = vec![Task::Search(s)];
    while let Some(task) = tasks.pop() {
        match task {
            Task::Search(v) => {
                path.push(NodeIndex::<Ix>::new(v));
                blocked[v] = true;
                tasks.push(Task::Unblock(v));
                if is_precessor_of_s[v] {
                    circuits.push(path.clone());
                }
                for &w in &perfgraph[v] {
                    debug_assert!(w > s);
                    if !blocked[w] {
                        tasks.push(Task::Search(w));
                    }
                }
            }
            Task::Unblock(v) => {
                blocked[v] = false;
                let popped = path.pop();
                debug_assert!(popped == Some(NodeIndex::<Ix>::new(v)));
            }
        }
    }
    debug_assert!(path.is_empty());
}

/// Finds and returns all elementary circuits in the graph.
/// Circuit is another word for cycle.
/// A circuit is called elementary, if it does not contain any node twice.
///
/// This function returns the same circuits as [Johnson's algorithm](https://www.cs.tufts.edu/comp/150GA/homeworks/hw1/Johnson%2075.PDF), although in a different order.
/// If I measured correctly, mine is faster.
///
/// # Example
/// ```
/// use petgraph::Graph;
/// use petgraph::Directed;
/// use graphalgs::elementary::elementary_circuits;
/// use petgraph::graph::NodeIndex;
///
/// fn n(i: usize) -> NodeIndex<usize> {
///     NodeIndex::new(i)
/// }
/// let graph = Graph::<(), (), Directed, usize>::from_edges([(1,2), (2,3), (3,1), (2,1)]);
/// let circuits = elementary_circuits(&graph);
/// assert_eq!(circuits, vec![vec![n(1),n(2)], vec![n(1),n(2),n(3)]]);
/// ```
pub fn elementary_circuits<N, E, Ix>(graph: &Graph<N, E, Directed, Ix>) -> Vec<Vec<NodeIndex<Ix>>>
where
    Ix: IndexType,
{
    let n = graph.node_count();
    let mut perfgraph = vec![Vec::new(); n];
    for e in graph.edge_references() {
        let source = e.source().index();
        let target = e.target().index();
        if !perfgraph[source].contains(&target) {
            perfgraph[source].push(target);
        }
    }
    let mut circuits = Vec::new();
    for s in 0..n {
        for vec in perfgraph.iter_mut() {
            vec.retain(|&x| x > s);
        }
        let is_precessor_of_s = (0..n)
            .map(|x| {
                graph
                    .edges_connecting(NodeIndex::<Ix>::new(x), NodeIndex::<Ix>::new(s))
                    .next()
                    .is_some()
            })
            .collect::<Vec<_>>();
        elementary_circuits_starting_at_s(&perfgraph, &is_precessor_of_s, &mut circuits, s);
    }
    circuits
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elementary_circuits_pairs() {
        let input_output_pairs = [
            (
                vec![(1, 3), (3, 1), (3, 2), (2, 3)],
                vec![vec![1, 3], vec![2, 3]],
            ),
            (
                vec![(1, 2), (2, 1), (2, 3), (4, 5), (5, 6), (6, 4)],
                vec![vec![1, 2], vec![4, 5, 6]],
            ),
            (vec![(2, 1), (1, 2), (3, 2), (3, 1)], vec![vec![1, 2]]),
            (
                vec![(1, 3), (3, 2), (3, 1), (2, 1)],
                vec![vec![1, 3], vec![1, 3, 2]],
            ),
            (
                vec![(1, 2), (2, 1), (2, 3), (2, 4), (4, 2)],
                vec![vec![1, 2], vec![2, 4]],
            ),
            // The tests above are from the Java Implementation
            // https://github.com/1123/johnson/blob/master/src/test/java/jgraphalgos/johnson/TestJohnson.java
            // of Johnson's algorithm. The tests below are not.
            (
                vec![(10, 30), (30, 10), (30, 20), (20, 30)],
                vec![vec![10, 30], vec![20, 30]],
            ),
            (
                vec![(3, 1), (1, 3), (3, 2), (2, 3)],
                vec![vec![1, 3], vec![2, 3]],
            ),
            (vec![(1, 2), (2, 3), (3, 4), (5, 6)], vec![]),
            (vec![], vec![]),
            (vec![(1, 1)], vec![vec![1]]),
            (vec![(1, 1), (1, 2), (2, 1)], vec![vec![1, 2], vec![1]]),
            (
                vec![(1, 2), (2, 1), (1, 3), (3, 1)],
                vec![vec![1, 3], vec![1, 2]],
            ),
            (
                vec![
                    (1, 1),
                    (1, 2),
                    (1, 3),
                    (2, 1),
                    (2, 2),
                    (2, 3),
                    (3, 1),
                    (3, 2),
                    (3, 3),
                ],
                vec![
                    vec![1, 3, 2],
                    vec![1, 3],
                    vec![1, 2, 3],
                    vec![1, 2],
                    vec![1],
                    vec![2, 3],
                    vec![2],
                    vec![3],
                ],
            ),
            (vec![(1, 2), (2, 1), (1, 2), (2, 1)], vec![vec![1, 2]]),
            (
                vec![(1, 2), (2, 3), (3, 1), (1, 2), (2, 3), (3, 1)],
                vec![vec![1, 2, 3]],
            ),
        ];
        for (input, expected_output) in input_output_pairs.iter() {
            let graph = Graph::<(), (), Directed, usize>::from_edges(input);
            let mut actual_output = elementary_circuits(&graph);
            let mut expected_output = expected_output
                .iter()
                .map(|path| {
                    path.iter()
                        .map(|&ni| NodeIndex::<usize>::new(ni))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            expected_output.sort();
            actual_output.sort();
            assert_eq!(actual_output, expected_output);
        }
    }
}
