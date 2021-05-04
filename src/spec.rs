//! Special algorithms that are difficult to categorize.
use std::collections::BinaryHeap;


/// Check whether the sequence of numbers is graph-like.
/// 
/// A sequence of non-negative integers is called a graph-like 
/// if it is a sequence of powers of some simple graph.
/// 
/// # Example
/// 
/// ```
/// use graphalgs::spec::is_degree_sequence_graphlike;
/// 
/// // Graph: [ 1-2-2-1 ] (the numbers are degrees of the vertices).
/// assert!(is_degree_sequence_graphlike(&vec![2, 2, 1, 1]));
/// 
/// // A single vertex of a graph cannot have degree 2.
/// assert!(!is_degree_sequence_graphlike(&vec![2]));
/// ```
pub fn is_degree_sequence_graphlike(degrees: &Vec<usize>) -> bool {
    // At each step of the algorithm, we remove the vertex with the maximum degree d,
    // and then try to reduce the d of the following degrees by 1. 
    // If at some point this becomes impossible, then this sequence is not a graph sequence.
    
    // The sum of the degrees of the vertices must be even.
    if degrees.iter().sum::<usize>() % 2 == 1 {
        return false;
    }
    
    // Isolated vertexes are not of interest.
    let mut degrees = degrees.into_iter()
        .map(|d| *d)
        .filter(|d| *d > 0usize)
        .collect::<BinaryHeap<usize>>();

    while degrees.len() > 0 {
        let d = degrees.pop().unwrap();
        if d > degrees.len() {
            return false;
        }
        
        let mut temp = Vec::<usize>::new();
        for _ in 0..d {
            let x = degrees.pop().unwrap();
            if x == 0 {
                return false;
            }
            temp.push(x-1);
        }

        for x in temp.into_iter() {
            if x != 0 {
                degrees.push(x);
            }
        }
    }

    true
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_the_degree_sequence_graphlike() {
        assert!(is_degree_sequence_graphlike(&vec![]));
        assert!(is_degree_sequence_graphlike(&vec![0]));
        assert!(!is_degree_sequence_graphlike(&vec![1]));
        assert!(!is_degree_sequence_graphlike(&vec![2]));
        assert!(!is_degree_sequence_graphlike(&vec![5]));
        assert!(is_degree_sequence_graphlike(&vec![1, 1]));
        assert!(!is_degree_sequence_graphlike(&vec![1, 2]));
        assert!(is_degree_sequence_graphlike(&vec![0, 0, 0]));
        assert!(!is_degree_sequence_graphlike(&vec![1, 1, 1]));
        assert!(!is_degree_sequence_graphlike(&vec![1, 2, 0]));
        assert!(is_degree_sequence_graphlike(&vec![1, 2, 1]));
        assert!(is_degree_sequence_graphlike(&vec![5, 5, 4, 3, 2, 2, 2, 1]));
        assert!(is_degree_sequence_graphlike(&vec![5, 3, 5, 5, 2, 2, 1, 1]));
        assert!(!is_degree_sequence_graphlike(&vec![5, 5, 5, 4, 2, 1, 1, 1]));
        assert!(is_degree_sequence_graphlike(&vec![1, 1, 1, 4, 2, 3, 1, 3, 1, 1]));
        assert!(!is_degree_sequence_graphlike(&vec![1, 1, 10, 4, 2, 3, 1, 3, 1, 1]));
    }
}
