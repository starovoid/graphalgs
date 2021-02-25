//! Special algorithms that are difficult to categorize.

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
/// assert!(is_degree_sequence_graphlike(vec![2, 2, 1, 1]));
/// 
/// // A single vertex of a graph cannot have degree 2.
/// assert!(!is_degree_sequence_graphlike(vec![2]));
/// ```
pub fn is_degree_sequence_graphlike(mut degrees: Vec<usize>) -> bool{
    // At each step of the algorithm, we remove the vertex with the maximum degree s,
    // and then try to reduce the s of the following degrees by 1. 
    // If at some point this becomes impossible, then this sequence is not a graph sequence.
    let mut length = degrees.len();

    while degrees.len() > 0 {
        degrees.sort();
        let d = degrees.pop().unwrap();
        length -= 1;

        for i in 1..=d {
            if i > length || degrees[length-i] == 0 {
                return false;
            }
            degrees[length-i] -= 1;
        }
    }
    true
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_the_degree_sequence_graphlike() {
        assert!(is_degree_sequence_graphlike(vec![]));
        assert!(is_degree_sequence_graphlike(vec![0]));
        assert!(!is_degree_sequence_graphlike(vec![1]));
        assert!(!is_degree_sequence_graphlike(vec![2]));
        assert!(!is_degree_sequence_graphlike(vec![5]));
        assert!(is_degree_sequence_graphlike(vec![1, 1]));
        assert!(!is_degree_sequence_graphlike(vec![1, 2]));
        assert!(is_degree_sequence_graphlike(vec![0, 0, 0]));
        assert!(!is_degree_sequence_graphlike(vec![1, 1, 1]));
        assert!(!is_degree_sequence_graphlike(vec![1, 2, 0]));
        assert!(is_degree_sequence_graphlike(vec![1, 2, 1]));
        assert!(is_degree_sequence_graphlike(vec![5, 5, 4, 3, 2, 2, 2, 1]));
        assert!(is_degree_sequence_graphlike(vec![5, 3, 5, 5, 2, 2, 1, 1]));
        assert!(!is_degree_sequence_graphlike(vec![5, 5, 5, 4, 2, 1, 1, 1]));
        assert!(is_degree_sequence_graphlike(vec![1, 1, 1, 4, 2, 3, 1, 3, 1, 1]));
        assert!(!is_degree_sequence_graphlike(vec![1, 1, 10, 4, 2, 3, 1, 3, 1, 1]));
    }
}