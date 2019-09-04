use std::iter::FromIterator;

#[derive(Default, Debug)]
pub struct Node<K, V> {
    key: K,
    value: V,
    size: usize,
    priority: u64,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
}

enum Travsal<T> {
    Left(T),
    Right(T),
}

impl<K: Ord, V> Node<K, V> {
    pub fn insert_or_replace(
        root: &mut Option<Box<Node<K, V>>>,
        new_node: Box<Node<K, V>>,
    ) -> Option<Box<Node<K, V>>> {
        // TODO:
        if let Some(ref mut root) = *root {
            root.insert(new_node)
        } else {
            *root = Some(new_node);
            None
        }
    }

    pub fn insert(&mut self, new_node: Box<Node<K, V>>) -> Option<Box<Node<K, V>>> {
        let ret = match self.key.cmp(&new_node.key) {
            std::cmp::Ordering::Equal => Some(new_node),
            std::cmp::Ordering::Greater => {
                let ret = Self::insert_or_replace(&mut self.left, new_node);
                if ret.is_none() {
                    self.size += 1;
                }
                if self.priority < self.left.as_ref().unwrap().priority {
                    self.rotate_right();
                }
                ret
            }
            std::cmp::Ordering::Less => {
                let ret = Self::insert_or_replace(&mut self.right, new_node);
                if ret.is_none() {
                    self.size += 1;
                }
                if self.priority < self.right.as_ref().unwrap().priority {
                    self.rotate_left();
                }
                ret
            }
        };

        ret
    }

    pub fn nth(&self, nth: usize) -> Option<(&K, &V)> {
        if nth >= self.size {
            return None;
        }

        let left_size = self.left.as_ref().map(|x| x.size).unwrap_or(0);
        if nth < left_size {
            self.left.as_ref().unwrap().nth(nth)
        } else if nth == left_size {
            Some((&self.key, &self.value))
        } else {
            self.right.as_ref().unwrap().nth(nth - left_size - 1)
        }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        match key.cmp(&self.key) {
            std::cmp::Ordering::Equal => Some(&self.value),
            std::cmp::Ordering::Less => self.left.as_ref().and_then(|node| node.get(key)),
            std::cmp::Ordering::Greater => self.right.as_ref().and_then(|node| node.get(key)),
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self._get_mut(key).map(|x| &mut x.value)
    }

    fn _get_mut(&mut self, key: &K) -> Option<&mut Self> {
        match key.cmp(&self.key) {
            std::cmp::Ordering::Equal => Some(self),
            std::cmp::Ordering::Less => self.left.as_mut().and_then(|node| node._get_mut(key)),
            std::cmp::Ordering::Greater => self.right.as_mut().and_then(|node| node._get_mut(key)),
        }
    }
    /// Remove the given key from the treap tree
    ///
    pub fn remove(node: &mut Option<Box<Node<K, V>>>) -> Option<Box<Node<K, V>>> {
        if node.is_none() {
            return None;
        }
        match **node.as_mut().unwrap() {
            Node {
                left: Some(ref mut b_left),
                right: Some(ref mut b_right),
                ..
            } => {
                if b_left.priority < b_right.priority {
                    node.as_mut().unwrap().rotate_left();
                    Self::remove(&mut node.as_mut().unwrap().left)
                } else {
                    node.as_mut().unwrap().rotate_right();
                    Self::remove(&mut node.as_mut().unwrap().right)
                }
            }
            Node {
                left: None,
                right: Some(_),
                ..
            } => {
                let right = node.as_mut().unwrap().right.take();
                std::mem::replace(node, right)
            }
            Node {
                left: Some(_),
                right: None,
                ..
            } => {
                let left = node.as_mut().unwrap().left.take();
                std::mem::replace(node, left)
            }
            _ => node.take(),
        }
    }

    fn rotate_left(&mut self) {
        let right = self.right.take();
        if let Some(mut node) = right {
            self.right = node.left.take();

            self.size -= node.size;
            node.size += self.size;
            self.size += self.right.as_ref().map(|x| x.size).unwrap_or(0);

            let old_root = std::mem::replace(self, *node);
            self.left = Some(Box::new(old_root));
        }
    }
    fn rotate_right(&mut self) {
        let left = self.left.take();
        if let Some(mut node) = left {
            self.left = node.right.take();

            self.size -= node.size;
            node.size += self.size;
            self.size += self.left.as_ref().map(|x| x.size).unwrap_or(0);

            let old_root = std::mem::replace(self, *node);
            self.right = Some(Box::new(old_root));
        }
    }

    fn mid_order_iter(&self) -> MidOrderIter<K, V> {
        MidOrderIter {
            nodes: vec![Travsal::Left(self)],
        }
    }
}

pub struct MidOrderIter<'a, K, V> {
    nodes: Vec<Travsal<&'a Node<K, V>>>,
}

impl<'a, K, V> Iterator for MidOrderIter<'a, K, V> {
    type Item = &'a Node<K, V>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.nodes.pop() {
                None => return None,
                Some(Travsal::Left(node)) => {
                    self.nodes.push(Travsal::Right(node));
                    if let Some(left) = &node.left {
                        self.nodes.push(Travsal::Left(&**left));
                    }
                }
                Some(Travsal::Right(node)) => return Some(node),
            }
        }
    }
}

#[derive(Debug)]
pub struct Treap<K, V>(Option<Box<Node<K, V>>>);

impl<K: Ord, V> Treap<K, V> {
    pub fn new() -> Treap<K, V> {
        Treap(None)
    }

    pub fn len(&self) -> usize {
        self.0.as_ref().map(|x| x.size).unwrap_or_default()
    }

    pub fn mid_order_iter(&self) -> MidOrderIter<K, V> {
        if let Some(ref node) = self.0 {
            MidOrderIter {
                nodes: vec![Travsal::Left(&**node)],
            }
        } else {
            MidOrderIter { nodes: vec![] }
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let new_node = Box::new(Node {
            key,
            value,
            size: 1,
            priority: rand::random(),
            left: None,
            right: None,
        });
        Node::insert_or_replace(&mut self.0, new_node).map(|x| x.value)
    }

    pub fn nth(&mut self, nth: usize) -> Option<(&K, &V)> {
        if self.0.is_none() {
            return None;
        }
        self.0.as_ref().unwrap().nth(nth)
    }
}

impl<K, V> Extend<(K, V)> for Treap<K, V>
where
    K: std::cmp::Ord,
{
    fn extend<E: IntoIterator<Item = (K, V)>>(&mut self, iter: E) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K, V> FromIterator<(K, V)> for Treap<K, V>
where
    K: std::cmp::Ord,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut c = Treap::new();
        for (k, v) in iter {
            c.insert(k, v);
        }
        c
    }
}

#[cfg(test)]
mod test {
    use super::Treap;
    #[test]
    fn test_rank1() {
        let mut tp = Treap::new();
        tp.insert(10, 100);
        tp.insert(11, 100);
        tp.insert(13, 100);
        assert_eq!(tp.nth(0), Some((&10, &100)));
        assert_eq!(tp.nth(1), Some((&11, &100)));
        assert_eq!(tp.nth(2), Some((&13, &100)));
    }
    #[test]
    fn test_rank2() {
        let mut tp = vec![
            (1, 2),
            (3, 4),
            (5, 6),
            (7, 8),
            (2, 3),
            (4, 5),
            (8, 9),
            (6, 7),
        ]
        .into_iter()
        .collect::<Treap<_, _>>();
        assert_eq!(tp.nth(0), Some((&1, &2)));
        assert_eq!(tp.nth(100), None);
        assert_eq!(tp.nth(tp.len()), None);
        assert_eq!(tp.nth(tp.len()-1), Some((&8, &9)));
    }

    #[test]
    fn test_remove() {
        let tp = vec![(1, 2), (3, 4), (5, 6)]
            .into_iter()
            .collect::<Treap<_, _>>();
        println!("{:?}", tp);
    }
    #[test]
    fn test_midorditer() {
        let tp = vec![
            (1, 2),
            (3, 4),
            (5, 6),
            (7, 8),
            (2, 3),
            (4, 5),
            (8, 9),
            (6, 7),
        ]
        .into_iter()
        .collect::<Treap<_, _>>();
        let tvec = tp.mid_order_iter().map(|node| node.key).collect::<Vec<_>>();
        assert_eq!(tvec.is_sorted(), true);
    }
}
