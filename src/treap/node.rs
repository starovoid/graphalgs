use crate::treap::entry::Entry;
use crate::treap::tree;

/// A struct representing an internal node of a treap.
pub struct Node<T, U> {
    pub entry: Entry<T, U>,
    pub priority: u32,
    pub len: usize,
    pub left: tree::Tree<T, U>,
    pub right: tree::Tree<T, U>,
}

impl<T, U> Node<T, U> {
    pub fn new(key: T, value: U, priority: u32) -> Self {
        Node {
            entry: Entry { key, value },
            priority,
            len: 1,
            left: None,
            right: None,
        }
    }

    pub fn update(&mut self) {
        let Node {
            ref mut len,
            ref left,
            ref right,
            ..
        } = self;
        *len = 1;
        if let Some(ref left_node) = left {
            *len += left_node.len;
        }
        if let Some(ref right_node) = right {
            *len += right_node.len;
        }
    }
}
