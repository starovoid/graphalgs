use std::cmp::Ordering;

pub struct Entry<T, U> {
    pub key: T,
    pub value: U,
}

impl<T, U> Ord for Entry<T, U>
where
    T: Ord,
{
    fn cmp(&self, other: &Entry<T, U>) -> Ordering {
        self.key.cmp(&other.key)
    }
}

impl<T, U> PartialOrd for Entry<T, U>
where
    T: Ord,
{
    fn partial_cmp(&self, other: &Entry<T, U>) -> Option<Ordering> {
        Some(self.key.cmp(&other.key))
    }
}

impl<T, U> PartialEq for Entry<T, U>
where
    T: Ord,
{
    fn eq(&self, other: &Entry<T, U>) -> bool {
        self.key == other.key
    }
}

impl<T, U> Eq for Entry<T, U> where T: Ord {}
