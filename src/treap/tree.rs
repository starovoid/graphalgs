use crate::treap::entry::Entry;
use crate::treap::node::Node;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::mem;

pub type Tree<T, U> = Option<Box<Node<T, U>>>;

pub fn merge<T, U>(l_tree: &mut Tree<T, U>, r_tree: Tree<T, U>) {
    match (l_tree.take(), r_tree) {
        (Some(mut l_node), Some(mut r_node)) => {
            if l_node.priority > r_node.priority {
                merge(&mut l_node.right, Some(r_node));
                l_node.update();
                *l_tree = Some(l_node);
            } else {
                let mut new_tree = Some(l_node);
                merge(&mut new_tree, r_node.left.take());
                r_node.left = new_tree;
                r_node.update();
                *l_tree = Some(r_node);
            }
        }
        (new_tree, None) | (None, new_tree) => *l_tree = new_tree,
    }
}

pub fn split<T, U, V>(tree: &mut Tree<T, U>, key: &V) -> (Tree<T, U>, Tree<T, U>)
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    match tree.take() {
        Some(mut node) => {
            let ret;
            match key.cmp(node.entry.key.borrow()) {
                Ordering::Less => {
                    let res = split(&mut node.left, key);
                    *tree = node.left.take();
                    node.left = res.1;
                    node.update();
                    ret = (res.0, Some(node));
                }
                Ordering::Greater => {
                    ret = split(&mut node.right, key);
                    node.update();
                    *tree = Some(node);
                }
                Ordering::Equal => {
                    *tree = node.left.take();
                    let right = node.right.take();
                    node.update();
                    ret = (Some(node), right);
                }
            }
            ret
        }
        None => (None, None),
    }
}

pub fn insert<T, U>(tree: &mut Tree<T, U>, mut new_node: Node<T, U>) -> Option<Entry<T, U>>
where
    T: Ord,
{
    match tree {
        Some(ref mut node) => {
            if new_node.priority <= node.priority {
                match new_node.entry.key.cmp(&node.entry.key) {
                    Ordering::Less => {
                        let ret = insert(&mut node.left, new_node);
                        node.update();
                        return ret;
                    }
                    Ordering::Greater => {
                        let ret = insert(&mut node.right, new_node);
                        node.update();
                        return ret;
                    }
                    Ordering::Equal => {
                        let Node { ref mut entry, .. } = &mut **node;
                        return Some(mem::replace(entry, new_node.entry));
                    }
                }
            }
        }
        None => {
            *tree = Some(Box::new(new_node));
            return None;
        }
    }
    new_node.left = tree.take();
    let (dup_opt, right) = split(&mut new_node.left, &new_node.entry.key);
    new_node.right = right;
    new_node.update();
    *tree = Some(Box::new(new_node));
    dup_opt.map(|node| node.entry)
}

pub fn remove<T, U, V>(tree: &mut Tree<T, U>, key: &V) -> Option<Entry<T, U>>
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    let mut new_tree;
    match tree {
        Some(ref mut node) => match key.cmp(node.entry.key.borrow()) {
            Ordering::Less => {
                let ret = remove(&mut node.left, key);
                node.update();
                return ret;
            }
            Ordering::Greater => {
                let ret = remove(&mut node.right, key);
                node.update();
                return ret;
            }
            Ordering::Equal => {
                new_tree = node.left.take();
                merge(&mut new_tree, node.right.take());
            }
        },
        None => return None,
    }
    mem::replace(tree, new_tree).map(|node| node.entry)
}

pub fn get<'a, T, U, V>(tree: &'a Tree<T, U>, key: &V) -> Option<&'a Entry<T, U>>
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    tree.as_ref()
        .and_then(|node| match key.cmp(node.entry.key.borrow()) {
            Ordering::Less => get(&node.left, key),
            Ordering::Greater => get(&node.right, key),
            Ordering::Equal => Some(&node.entry),
        })
}

pub fn get_mut<'a, T, U, V>(tree: &'a mut Tree<T, U>, key: &V) -> Option<&'a mut Entry<T, U>>
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    tree.as_mut()
        .and_then(|node| match key.cmp(node.entry.key.borrow()) {
            Ordering::Less => get_mut(&mut node.left, key),
            Ordering::Greater => get_mut(&mut node.right, key),
            Ordering::Equal => Some(&mut node.entry),
        })
}

pub fn ceil<'a, T, U, V>(tree: &'a Tree<T, U>, key: &V) -> Option<&'a Entry<T, U>>
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    tree.as_ref()
        .and_then(|node| match key.cmp(node.entry.key.borrow()) {
            Ordering::Greater => ceil(&node.right, key),
            Ordering::Less => match ceil(&node.left, key) {
                None => Some(&node.entry),
                res => res,
            },
            Ordering::Equal => Some(&node.entry),
        })
}

pub fn floor<'a, T, U, V>(tree: &'a Tree<T, U>, key: &V) -> Option<&'a Entry<T, U>>
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    tree.as_ref()
        .and_then(|node| match key.cmp(node.entry.key.borrow()) {
            Ordering::Less => floor(&node.left, key),
            Ordering::Greater => match floor(&node.right, key) {
                None => Some(&node.entry),
                res => res,
            },
            Ordering::Equal => Some(&node.entry),
        })
}

pub fn min<T, U>(tree: &Tree<T, U>) -> Option<&Entry<T, U>>
where
    T: Ord,
{
    tree.as_ref().and_then(|node| {
        let mut curr = node;
        while let Some(ref left_node) = curr.left {
            curr = left_node;
        }
        Some(&curr.entry)
    })
}

pub fn max<T, U>(tree: &Tree<T, U>) -> Option<&Entry<T, U>>
where
    T: Ord,
{
    tree.as_ref().and_then(|node| {
        let mut curr = node;
        while let Some(ref right_node) = curr.right {
            curr = right_node;
        }
        Some(&curr.entry)
    })
}

pub fn union<T, U>(left_tree: Tree<T, U>, right_tree: Tree<T, U>, mut swapped: bool) -> Tree<T, U>
where
    T: Ord,
{
    match (left_tree, right_tree) {
        (Some(mut left_node), Some(mut right_node)) => {
            if left_node.priority < right_node.priority {
                mem::swap(&mut left_node, &mut right_node);
                swapped = !swapped;
            }
            {
                let Node {
                    left: ref mut left_subtree,
                    right: ref mut right_subtree,
                    ref mut entry,
                    ..
                } = &mut *left_node;
                let mut right_left_subtree = Some(right_node);
                let (dup_opt, right_right_subtree) = split(&mut right_left_subtree, &entry.key);
                *left_subtree = union(left_subtree.take(), right_left_subtree, swapped);
                *right_subtree = union(right_subtree.take(), right_right_subtree, swapped);
                if let Some(dup_node) = dup_opt {
                    if swapped {
                        *entry = dup_node.entry;
                    }
                }
            }
            left_node.update();
            Some(left_node)
        }
        (None, right_tree) => right_tree,
        (left_tree, None) => left_tree,
    }
}

pub fn intersection<T, U>(
    left_tree: Tree<T, U>,
    right_tree: Tree<T, U>,
    mut swapped: bool,
) -> Tree<T, U>
where
    T: Ord,
{
    match (left_tree, right_tree) {
        (Some(mut left_node), Some(mut right_node)) => {
            {
                if left_node.priority < right_node.priority {
                    mem::swap(&mut left_node, &mut right_node);
                    swapped = !swapped;
                }
                let Node {
                    left: ref mut left_subtree,
                    right: ref mut right_subtree,
                    ref mut entry,
                    ..
                } = &mut *left_node;
                let mut right_left_subtree = Some(right_node);
                let (dup_opt, right_right_subtree) = split(&mut right_left_subtree, &entry.key);
                *left_subtree = intersection(left_subtree.take(), right_left_subtree, swapped);
                *right_subtree = intersection(right_subtree.take(), right_right_subtree, swapped);
                match dup_opt {
                    Some(dup_node) => {
                        if swapped {
                            *entry = dup_node.entry;
                        }
                    }
                    None => {
                        merge(left_subtree, right_subtree.take());
                        return left_subtree.take();
                    }
                }
            }
            left_node.update();
            Some(left_node)
        }
        _ => None,
    }
}

pub fn difference<T, U>(
    left_tree: Tree<T, U>,
    right_tree: Tree<T, U>,
    mut swapped: bool,
    symmetric: bool,
) -> Tree<T, U>
where
    T: Ord,
{
    match (left_tree, right_tree) {
        (Some(mut left_node), Some(mut right_node)) => {
            {
                if left_node.priority < right_node.priority {
                    mem::swap(&mut left_node, &mut right_node);
                    swapped = !swapped;
                }
                let Node {
                    left: ref mut left_subtree,
                    right: ref mut right_subtree,
                    ref mut entry,
                    ..
                } = &mut *left_node;
                let mut right_left_subtree = Some(right_node);
                let (dup_opt, right_right_subtree) = split(&mut right_left_subtree, &entry.key);
                *left_subtree =
                    difference(left_subtree.take(), right_left_subtree, swapped, symmetric);
                *right_subtree = difference(
                    right_subtree.take(),
                    right_right_subtree,
                    swapped,
                    symmetric,
                );
                if dup_opt.is_some() || (swapped && !symmetric) {
                    merge(left_subtree, right_subtree.take());
                    return left_subtree.take();
                }
            }
            left_node.update();
            Some(left_node)
        }
        (mut left_tree, right_tree) => {
            if symmetric {
                merge(&mut left_tree, right_tree);
                left_tree
            } else if swapped {
                right_tree
            } else {
                left_tree
            }
        }
    }
}
