use crate::treap::entry::Entry;
use crate::treap::node::Node;
use crate::treap::tree;
use rand::rngs::StdRng;
use rand::{RngCore, SeedableRng};
use std::borrow::Borrow;
use std::ops::{Add, Index, IndexMut, Sub};

/// An ordered map implemented using a treap.
///
/// A treap is a tree that satisfies both the binary search tree property and a heap property. Each
/// node has a key, a value, and a priority. The key of any node is greater than all keys in its
/// left subtree and less than all keys occuring in its right subtree. The priority of a node is
/// greater than the priority of all nodes in its subtrees. By randomly generating priorities, the
/// expected height of the tree is proportional to the logarithm of the number of keys.
///
/// # Examples
///
/// ```
/// use extended_collections::treap::TreapMap;
///
/// let mut map = TreapMap::new();
/// map.insert(0, 1);
/// map.insert(3, 4);
///
/// assert_eq!(map[&0], 1);
/// assert_eq!(map.get(&1), None);
/// assert_eq!(map.len(), 2);
///
/// assert_eq!(map.min(), Some(&0));
/// assert_eq!(map.ceil(&2), Some(&3));
///
/// map[&0] = 2;
/// assert_eq!(map.remove(&0), Some((0, 2)));
/// assert_eq!(map.remove(&1), None);
/// ```
pub struct TreapMap<T, U> {
    tree: tree::Tree<T, U>,
    rng: StdRng,
}

impl<T, U> TreapMap<T, U> {
    /// Constructs a new, empty `TreapMap<T, U>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let map: TreapMap<u32, u32> = TreapMap::new();
    /// ```
    pub fn new() -> Self {
        TreapMap {
            tree: None,
            rng: StdRng::from_entropy(),
        }
    }

    /// Inserts a key-value pair into the map. If the key already exists in the map, it will return
    /// and replace the old key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// assert_eq!(map.insert(1, 1), None);
    /// assert_eq!(map.get(&1), Some(&1));
    /// assert_eq!(map.insert(1, 2), Some((1, 1)));
    /// assert_eq!(map.get(&1), Some(&2));
    /// ```
    pub fn insert(&mut self, key: T, value: U) -> Option<(T, U)>
    where
        T: Ord,
    {
        let TreapMap {
            ref mut tree,
            ref mut rng,
        } = self;
        let new_node = Node::new(key, value, rng.next_u32());
        tree::insert(tree, new_node).and_then(|entry| {
            let Entry { key, value } = entry;
            Some((key, value))
        })
    }

    /// Removes a key-value pair from the map. If the key exists in the map, it will return the
    /// associated key-value pair. Otherwise it will return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.remove(&1), Some((1, 1)));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<V>(&mut self, key: &V) -> Option<(T, U)>
    where
        T: Borrow<V>,
        V: Ord + ?Sized,
    {
        let TreapMap { ref mut tree, .. } = self;
        tree::remove(tree, key).and_then(|entry| {
            let Entry { key, value } = entry;
            Some((key, value))
        })
    }

    /// Checks if a key exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// assert!(!map.contains_key(&0));
    /// assert!(map.contains_key(&1));
    /// ```
    pub fn contains_key<V>(&self, key: &V) -> bool
    where
        T: Borrow<V>,
        V: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    /// Returns an immutable reference to the value associated with a particular key. It will
    /// return `None` if the key does not exist in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.get(&0), None);
    /// assert_eq!(map.get(&1), Some(&1));
    /// ```
    pub fn get<V>(&self, key: &V) -> Option<&U>
    where
        T: Borrow<V>,
        V: Ord + ?Sized,
    {
        tree::get(&self.tree, key).map(|entry| &entry.value)
    }

    /// Returns a mutable reference to the value associated with a particular key. Returns `None`
    /// if such a key does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// *map.get_mut(&1).unwrap() = 2;
    /// assert_eq!(map.get(&1), Some(&2));
    /// ```
    pub fn get_mut<V>(&mut self, key: &V) -> Option<&mut U>
    where
        T: Borrow<V>,
        V: Ord + ?Sized,
    {
        tree::get_mut(&mut self.tree, key).map(|entry| &mut entry.value)
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        match self.tree {
            None => 0,
            Some(ref node) => node.len,
        }
    }

    /// Returns `true` if the map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let map: TreapMap<u32, u32> = TreapMap::new();
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the map, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// map.insert(2, 2);
    /// map.clear();
    /// assert_eq!(map.is_empty(), true);
    /// ```
    pub fn clear(&mut self) {
        self.tree = None;
    }

    /// Returns a key in the map that is less than or equal to a particular key. Returns `None` if
    /// such a key does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.floor(&0), None);
    /// assert_eq!(map.floor(&2), Some(&1));
    /// ```
    pub fn floor<V>(&self, key: &V) -> Option<&T>
    where
        T: Borrow<V>,
        V: Ord + ?Sized,
    {
        tree::floor(&self.tree, key).map(|entry| &entry.key)
    }

    /// Returns a key in the map that is greater than or equal to a particular key. Returns `None`
    /// if such a key does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.ceil(&0), Some(&1));
    /// assert_eq!(map.ceil(&2), None);
    /// ```
    pub fn ceil<V>(&self, key: &V) -> Option<&T>
    where
        T: Borrow<V>,
        V: Ord + ?Sized,
    {
        tree::ceil(&self.tree, key).map(|entry| &entry.key)
    }

    /// Returns the minimum key of the map. Returns `None` if the map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// map.insert(3, 3);
    /// assert_eq!(map.min(), Some(&1));
    /// ```
    pub fn min(&self) -> Option<&T>
    where
        T: Ord,
    {
        tree::min(&self.tree).map(|entry| &entry.key)
    }

    /// Returns the maximum key of the map. Returns `None` if the map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// map.insert(3, 3);
    /// assert_eq!(map.max(), Some(&3));
    /// ```
    pub fn max(&self) -> Option<&T>
    where
        T: Ord,
    {
        tree::max(&self.tree).map(|entry| &entry.key)
    }

    /// Splits the map and returns the right part of the map. If `inclusive` is true, then the map
    /// will retain the given key if it exists. Otherwise, the right part of the map will contain
    /// the key if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// map.insert(2, 2);
    /// map.insert(3, 3);
    ///
    /// let split = map.split_off(&2, true);
    /// assert_eq!(map[&1], 1);
    /// assert_eq!(map[&2], 2);
    /// assert_eq!(split[&3], 3);
    /// ```
    pub fn split_off<V>(&mut self, key: &V, inclusive: bool) -> Self
    where
        T: Borrow<V>,
        V: Ord + ?Sized,
    {
        let TreapMap { ref mut tree, .. } = self;
        let (mut split_node, ret) = tree::split(tree, key);
        if inclusive {
            tree::merge(tree, split_node);
            TreapMap {
                tree: ret,
                rng: StdRng::from_entropy(),
            }
        } else {
            tree::merge(&mut split_node, ret);
            TreapMap {
                tree: split_node,
                rng: StdRng::from_entropy(),
            }
        }
    }

    /// Returns the union of two maps. If there is a key that is found in both `left` and `right`,
    /// the union will contain the value associated with the key in `left`. The `+`
    /// operator is implemented to take the union of two maps.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut n = TreapMap::new();
    /// n.insert(1, 1);
    /// n.insert(2, 2);
    ///
    /// let mut m = TreapMap::new();
    /// m.insert(2, 3);
    /// m.insert(3, 3);
    ///
    /// let union = TreapMap::union(n, m);
    /// assert_eq!(
    ///     union.iter().collect::<Vec<(&u32, &u32)>>(),
    ///     vec![(&1, &1), (&2, &2), (&3, &3)],
    /// );
    /// ```
    pub fn union(left: Self, right: Self) -> Self
    where
        T: Ord,
    {
        let TreapMap {
            tree: left_tree,
            rng,
        } = left;
        let TreapMap {
            tree: right_tree, ..
        } = right;
        TreapMap {
            tree: tree::union(left_tree, right_tree, false),
            rng,
        }
    }

    /// Returns the intersection of two maps. If there is a key that is found in both `left` and
    /// `right`, the intersection will contain the value associated with the key in `left`.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut n = TreapMap::new();
    /// n.insert(1, 1);
    /// n.insert(2, 2);
    ///
    /// let mut m = TreapMap::new();
    /// m.insert(2, 3);
    /// m.insert(3, 3);
    ///
    /// let intersection = TreapMap::intersection(n, m);
    /// assert_eq!(
    ///     intersection.iter().collect::<Vec<(&u32, &u32)>>(),
    ///     vec![(&2, &2)],
    /// );
    /// ```
    pub fn intersection(left: Self, right: Self) -> Self
    where
        T: Ord,
    {
        let TreapMap {
            tree: left_tree,
            rng,
        } = left;
        TreapMap {
            tree: tree::intersection(left_tree, right.tree, false),
            rng,
        }
    }

    /// Returns the difference of `left` and `right`. The returned map will contain all entries
    /// that do not have a key in `right`. The `-` operator is implemented to take the difference
    /// of two maps.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut n = TreapMap::new();
    /// n.insert(1, 1);
    /// n.insert(2, 2);
    ///
    /// let mut m = TreapMap::new();
    /// m.insert(2, 3);
    /// m.insert(3, 3);
    ///
    /// let difference = TreapMap::difference(n, m);
    /// assert_eq!(
    ///     difference.iter().collect::<Vec<(&u32, &u32)>>(),
    ///     vec![(&1, &1)],
    /// );
    /// ```
    pub fn difference(left: Self, right: Self) -> Self
    where
        T: Ord,
    {
        let TreapMap {
            tree: left_tree,
            rng,
        } = left;
        TreapMap {
            tree: tree::difference(left_tree, right.tree, false, false),
            rng,
        }
    }

    /// Returns the symmetric difference of `left` and `right`. The returned map will contain all
    /// entries that exist in one map, but not both maps.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut n = TreapMap::new();
    /// n.insert(1, 1);
    /// n.insert(2, 2);
    ///
    /// let mut m = TreapMap::new();
    /// m.insert(2, 3);
    /// m.insert(3, 3);
    ///
    /// let symmetric_difference = TreapMap::symmetric_difference(n, m);
    /// assert_eq!(
    ///     symmetric_difference.iter().collect::<Vec<(&u32, &u32)>>(),
    ///     vec![(&1, &1), (&3, &3)],
    /// );
    /// ```
    pub fn symmetric_difference(left: Self, right: Self) -> Self
    where
        T: Ord,
    {
        let TreapMap {
            tree: left_tree,
            rng,
        } = left;
        let TreapMap {
            tree: right_tree, ..
        } = right;
        TreapMap {
            tree: tree::difference(left_tree, right_tree, false, true),
            rng,
        }
    }

    /// Returns an iterator over the map. The iterator will yield key-value pairs using in-order
    /// traversal.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// map.insert(2, 2);
    ///
    /// let mut iterator = map.iter();
    /// assert_eq!(iterator.next(), Some((&1, &1)));
    /// assert_eq!(iterator.next(), Some((&2, &2)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter(&self) -> TreapMapIter<'_, T, U> {
        TreapMapIter {
            current: &self.tree,
            stack: Vec::new(),
        }
    }

    /// Returns a mutable iterator over the map. The iterator will yield key-value pairs using
    /// in-order traversal.
    ///
    /// # Examples
    ///
    /// ```
    /// use extended_collections::treap::TreapMap;
    ///
    /// let mut map = TreapMap::new();
    /// map.insert(1, 1);
    /// map.insert(2, 2);
    ///
    /// for (key, value) in &mut map {
    ///     *value += 1;
    /// }
    ///
    /// let mut iterator = map.iter_mut();
    /// assert_eq!(iterator.next(), Some((&1, &mut 2)));
    /// assert_eq!(iterator.next(), Some((&2, &mut 3)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> TreapMapIterMut<'_, T, U> {
        TreapMapIterMut {
            current: self.tree.as_mut().map(|node| &mut **node),
            stack: Vec::new(),
        }
    }
}

impl<T, U> IntoIterator for TreapMap<T, U> {
    type IntoIter = TreapMapIntoIter<T, U>;
    type Item = (T, U);

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            current: self.tree,
            stack: Vec::new(),
        }
    }
}

impl<'a, T, U> IntoIterator for &'a TreapMap<T, U>
where
    T: 'a,
    U: 'a,
{
    type IntoIter = TreapMapIter<'a, T, U>;
    type Item = (&'a T, &'a U);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, U> IntoIterator for &'a mut TreapMap<T, U>
where
    T: 'a,
    U: 'a,
{
    type IntoIter = TreapMapIterMut<'a, T, U>;
    type Item = (&'a T, &'a mut U);

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An owning iterator for `TreapMap<T, U>`.
///
/// This iterator traverses the elements of the map in-order and yields owned entries.
pub struct TreapMapIntoIter<T, U> {
    current: tree::Tree<T, U>,
    stack: Vec<Node<T, U>>,
}

impl<T, U> Iterator for TreapMapIntoIter<T, U> {
    type Item = (T, U);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut node) = self.current.take() {
            self.current = node.left.take();
            self.stack.push(*node);
        }
        self.stack.pop().map(|node| {
            let Node {
                entry: Entry { key, value },
                right,
                ..
            } = node;
            self.current = right;
            (key, value)
        })
    }
}

/// An iterator for `TreapMap<T, U>`.
///
/// This iterator traverses the elements of the map in-order and yields immutable references.
pub struct TreapMapIter<'a, T, U> {
    current: &'a tree::Tree<T, U>,
    stack: Vec<&'a Node<T, U>>,
}

impl<'a, T, U> Iterator for TreapMapIter<'a, T, U>
where
    T: 'a,
    U: 'a,
{
    type Item = (&'a T, &'a U);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(ref node) = self.current {
            self.current = &node.left;
            self.stack.push(node);
        }
        self.stack.pop().map(|node| {
            let Node {
                entry: Entry { ref key, ref value },
                ref right,
                ..
            } = node;
            self.current = right;
            (key, value)
        })
    }
}

type BorrowedIterEntryMut<'a, T, U> = Option<(&'a mut Entry<T, U>, BorrowedTreeMut<'a, T, U>)>;
type BorrowedTreeMut<'a, T, U> = Option<&'a mut Node<T, U>>;

/// A mutable iterator for `TreapMap<T, U>`.
///
/// This iterator traverses the elements of the map in-order and yields mutable references.
pub struct TreapMapIterMut<'a, T, U> {
    current: Option<&'a mut Node<T, U>>,
    stack: Vec<BorrowedIterEntryMut<'a, T, U>>,
}

impl<'a, T, U> Iterator for TreapMapIterMut<'a, T, U>
where
    T: 'a,
    U: 'a,
{
    type Item = (&'a T, &'a mut U);

    fn next(&mut self) -> Option<Self::Item> {
        let TreapMapIterMut {
            ref mut current,
            ref mut stack,
        } = self;
        while current.is_some() {
            stack.push(current.take().map(|node| {
                *current = node.left.as_mut().map(|node| &mut **node);
                (&mut node.entry, node.right.as_mut().map(|node| &mut **node))
            }));
        }
        stack.pop().and_then(|pair_opt| match pair_opt {
            Some(pair) => {
                let (entry, right) = pair;
                let Entry {
                    ref key,
                    ref mut value,
                } = entry;
                *current = right;
                Some((key, value))
            }
            None => None,
        })
    }
}

impl<T, U> Default for TreapMap<T, U> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, U> Add for TreapMap<T, U>
where
    T: Ord,
{
    type Output = TreapMap<T, U>;

    fn add(self, other: TreapMap<T, U>) -> TreapMap<T, U> {
        Self::union(self, other)
    }
}

impl<T, U> Sub for TreapMap<T, U>
where
    T: Ord,
{
    type Output = TreapMap<T, U>;

    fn sub(self, other: TreapMap<T, U>) -> TreapMap<T, U> {
        Self::difference(self, other)
    }
}

impl<'a, T, U, V> Index<&'a V> for TreapMap<T, U>
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    type Output = U;

    fn index(&self, key: &V) -> &Self::Output {
        self.get(key).expect("Error: key does not exist.")
    }
}

impl<'a, T, U, V> IndexMut<&'a V> for TreapMap<T, U>
where
    T: Borrow<V>,
    V: Ord + ?Sized,
{
    fn index_mut(&mut self, key: &V) -> &mut Self::Output {
        self.get_mut(key).expect("Error: key does not exist.")
    }
}

#[cfg(test)]
mod tests {
    use super::TreapMap;

    #[test]
    fn test_len_empty() {
        let map: TreapMap<u32, u32> = TreapMap::new();
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_is_empty() {
        let map: TreapMap<u32, u32> = TreapMap::new();
        assert!(map.is_empty());
    }

    #[test]
    fn test_min_max_empty() {
        let map: TreapMap<u32, u32> = TreapMap::new();
        assert_eq!(map.min(), None);
        assert_eq!(map.max(), None);
    }

    #[test]
    fn test_insert() {
        let mut map = TreapMap::new();
        assert_eq!(map.insert(1, 1), None);
        assert!(map.contains_key(&1));
        assert_eq!(map.get(&1), Some(&1));
    }

    #[test]
    fn test_insert_replace() {
        let mut map = TreapMap::new();
        assert_eq!(map.insert(1, 1), None);
        assert_eq!(map.insert(1, 3), Some((1, 1)));
        assert_eq!(map.get(&1), Some(&3));
    }

    #[test]
    fn test_remove() {
        let mut map = TreapMap::new();
        map.insert(1, 1);
        assert_eq!(map.remove(&1), Some((1, 1)));
        assert!(!map.contains_key(&1));
    }

    #[test]
    fn test_min_max() {
        let mut map = TreapMap::new();
        map.insert(1, 1);
        map.insert(3, 3);
        map.insert(5, 5);

        assert_eq!(map.min(), Some(&1));
        assert_eq!(map.max(), Some(&5));
    }

    #[test]
    fn test_get_mut() {
        let mut map = TreapMap::new();
        map.insert(1, 1);
        {
            let value = map.get_mut(&1);
            *value.unwrap() = 3;
        }
        assert_eq!(map.get(&1), Some(&3));
    }

    #[test]
    fn test_floor_ceil() {
        let mut map = TreapMap::new();
        map.insert(1, 1);
        map.insert(3, 3);
        map.insert(5, 5);

        assert_eq!(map.floor(&0), None);
        assert_eq!(map.floor(&2), Some(&1));
        assert_eq!(map.floor(&4), Some(&3));
        assert_eq!(map.floor(&6), Some(&5));

        assert_eq!(map.ceil(&0), Some(&1));
        assert_eq!(map.ceil(&2), Some(&3));
        assert_eq!(map.ceil(&4), Some(&5));
        assert_eq!(map.ceil(&6), None);
    }

    #[test]
    fn test_split_off_inclusive() {
        let mut map = TreapMap::new();
        map.insert(1, 1);
        map.insert(2, 2);
        map.insert(3, 3);

        let split = map.split_off(&2, true);
        assert_eq!(
            map.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&1, &1), (&2, &2)],
        );
        assert_eq!(split.iter().collect::<Vec<(&u32, &u32)>>(), vec![(&3, &3)]);
    }

    #[test]
    fn test_split_off_not_inclusive() {
        let mut map = TreapMap::new();
        map.insert(1, 1);
        map.insert(2, 2);
        map.insert(3, 3);

        let split = map.split_off(&2, false);
        assert_eq!(map.iter().collect::<Vec<(&u32, &u32)>>(), vec![(&1, &1)]);
        assert_eq!(
            split.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&2, &2), (&3, &3)],
        );
    }

    #[test]
    fn test_union() {
        let mut n = TreapMap::new();
        n.insert(1, 1);
        n.insert(2, 2);
        n.insert(3, 3);

        let mut m = TreapMap::new();
        m.insert(3, 5);
        m.insert(4, 4);
        m.insert(5, 5);

        let union = n + m;

        assert_eq!(
            union.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&1, &1), (&2, &2), (&3, &3), (&4, &4), (&5, &5)],
        );
        assert_eq!(union.len(), 5);
    }

    #[test]
    fn test_intersection() {
        let mut n = TreapMap::new();
        n.insert(1, 1);
        n.insert(2, 2);
        n.insert(3, 3);

        let mut m = TreapMap::new();
        m.insert(3, 5);
        m.insert(4, 4);
        m.insert(5, 5);

        let intersection = TreapMap::intersection(n, m);

        assert_eq!(
            intersection.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&3, &3)],
        );
        assert_eq!(intersection.len(), 1);
    }

    #[test]
    fn test_difference() {
        let mut n = TreapMap::new();
        n.insert(1, 1);
        n.insert(2, 2);
        n.insert(3, 3);

        let mut m = TreapMap::new();
        m.insert(3, 5);
        m.insert(4, 4);
        m.insert(5, 5);

        let difference = n - m;

        assert_eq!(
            difference.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&1, &1), (&2, &2)],
        );
        assert_eq!(difference.len(), 2);
    }

    #[test]
    fn test_symmetric_difference() {
        let mut n = TreapMap::new();
        n.insert(1, 1);
        n.insert(2, 2);
        n.insert(3, 3);

        let mut m = TreapMap::new();
        m.insert(3, 5);
        m.insert(4, 4);
        m.insert(5, 5);

        let symmetric_difference = TreapMap::symmetric_difference(n, m);

        assert_eq!(
            symmetric_difference.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&1, &1), (&2, &2), (&4, &4), (&5, &5)],
        );
        assert_eq!(symmetric_difference.len(), 4);
    }

    #[test]
    fn test_into_iter() {
        let mut map = TreapMap::new();
        map.insert(1, 2);
        map.insert(5, 6);
        map.insert(3, 4);

        assert_eq!(
            map.into_iter().collect::<Vec<(u32, u32)>>(),
            vec![(1, 2), (3, 4), (5, 6)],
        );
    }

    #[test]
    fn test_iter() {
        let mut map = TreapMap::new();
        map.insert(1, 2);
        map.insert(5, 6);
        map.insert(3, 4);

        assert_eq!(
            map.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&1, &2), (&3, &4), (&5, &6)],
        );
    }

    #[test]
    fn test_iter_mut() {
        let mut map = TreapMap::new();
        map.insert(1, 2);
        map.insert(5, 6);
        map.insert(3, 4);

        for (_, value) in &mut map {
            *value += 1;
        }

        assert_eq!(
            map.iter().collect::<Vec<(&u32, &u32)>>(),
            vec![(&1, &3), (&3, &5), (&5, &7)],
        );
    }
}
