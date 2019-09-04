use std::iter::FromIterator;
use std::ops::{Index, IndexMut};

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
        if let Some(ref mut root) = *root {
            root.insert(new_node)
        } else {
            *root = Some(new_node);
            None
        }
    }

    pub fn insert(&mut self, new_node: Box<Node<K, V>>) -> Option<Box<Node<K, V>>> {
        match self.key.cmp(&new_node.key) {
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
        }
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

    pub fn get(&self, key: &K) -> Option<&Node<K, V>> {
        match key.cmp(&self.key) {
            std::cmp::Ordering::Equal => Some(self),
            std::cmp::Ordering::Less => self.left.as_ref()?.get(key),
            std::cmp::Ordering::Greater => self.right.as_ref()?.get(key),
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut Node<K, V>> {
        match key.cmp(&self.key) {
            std::cmp::Ordering::Equal => Some(self),
            std::cmp::Ordering::Less => self.left.as_mut()?.get_mut(key),
            std::cmp::Ordering::Greater => self.right.as_mut()?.get_mut(key),
        }
    }

    /// Remove the given key from the treap tree
    ///
    fn _remove(node: &mut Option<Box<Node<K, V>>>) -> Option<Box<Node<K, V>>> {
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
        if let Some(mut node) = self.right.take() {
            self.right = node.left.take();

            self.size -= node.size;
            node.size += self.size;
            self.size += self.right.as_ref().map(|x| x.size).unwrap_or(0);

            let old_root = std::mem::replace(self, *node);
            self.left = Some(Box::new(old_root));
        }
    }
    fn rotate_right(&mut self) {
        if let Some(mut node) = self.left.take() {
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

    // in bfs order，maybe changed later.
    fn iter(&self) -> Iter<K, V> {
        Iter { nodes: vec![self] }
    }
}

pub struct Iter<'a, K, V> {
    nodes: Vec<&'a Node<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = &'a Node<K, V>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.nodes.pop() {
            if let Some(x) = node.left.as_ref() {
                self.nodes.push(x);
            }
            if let Some(x) = node.right.as_ref() {
                self.nodes.push(x);
            }

            Some(node)
        } else {
            None
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

impl<K, V> Default for Treap<K, V> {
    fn default() -> Self {
        Treap(None)
    }
}

impl<'a, K: Ord, V> Index<&'a K> for Treap<K, V> {
    type Output = V;

    fn index(&self, key: &K) -> &Self::Output {
        let msg = "no entry for key";
        &self.0.as_ref().expect(msg).get(key).expect(msg).value
    }
}

impl<'a, K: Ord, V> IndexMut<&'a K> for Treap<K, V> {
    /// Performs the mutable indexing (`container[index]`) operation.
    fn index_mut(&mut self, key: &K) -> &mut Self::Output {
        let msg = "no entry for key";
        &mut self.0.as_mut().expect(msg).get_mut(key).expect(msg).value
    }
}

impl<K: Ord, V> Treap<K, V> {
    pub fn new() -> Treap<K, V> {
        Default::default()
    }

    pub fn len(&self) -> usize {
        self.0.as_ref().map(|x| x.size).unwrap_or_default()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn contains(&self, key: &K) -> bool {
        self.0.as_ref().and_then(|x| x.get(key)).is_some()
    }

    pub fn mid_order_iter(&self) -> MidOrderIter<K, V> {
        self.0
            .as_ref()
            .map(|x| x.mid_order_iter())
            .unwrap_or(MidOrderIter { nodes: vec![] })
    }
    pub fn iter(&self) -> Iter<K, V> {
        self.0
            .as_ref()
            .map(|x| x.iter())
            .unwrap_or(Iter { nodes: vec![] })
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
        self.0.as_ref()?.nth(nth)
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
    use super::Iter;
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
        assert_eq!(tp.nth(tp.len() - 1), Some((&8, &9)));
    }

    #[test]
    fn test_remove() {
        let tp = vec![(1, 2), (3, 4), (5, 6)]
            .into_iter()
            .collect::<Treap<_, _>>();
        // println!("{:?}", tp);
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
    #[test]
    fn test_node_size() {
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
        for n in tp.0.as_ref().unwrap().iter() {
            assert_eq!(
                n.size,
                1 + n.left.as_ref().iter().map(|node| node.size).sum::<usize>()
                    + n.right.as_ref().iter().map(|node| node.size).sum::<usize>()
            )
        }
        let tvec = tp.0.as_ref().unwrap().iter().collect::<Vec<_>>();
        assert_eq!(tvec.len(), tp.len());
        assert_eq!(tp.is_empty(), false);
    }
    #[test]
    fn test_node_mid_order_iter() {
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
        for n in tp.0.as_ref().unwrap().iter() {
            assert_eq!(
                n.size,
                1 + n.left.as_ref().map(|node| node.size).unwrap_or(0)
                    + n.right.as_ref().map(|node| node.size).unwrap_or(0)
            );
        }
        for n in tp.0.as_ref().unwrap().iter() {
            assert_eq!(
                n.size,
                1 + n
                    .left
                    .as_ref()
                    .map(|x| x.iter())
                    .unwrap_or(Iter { nodes: vec![] })
                    .count()
                    + n.right
                        .as_ref()
                        .map(|x| x.iter())
                        .unwrap_or(Iter { nodes: vec![] })
                        .count()
            );
        }

        let tvec = tp.0.as_ref().unwrap().iter().collect::<Vec<_>>();
        assert_eq!(tvec.len(), tp.len());
        assert_eq!(tp.is_empty(), false);
    }
    #[test]
    fn test_iter() {
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
        let tvec = tp.iter().collect::<Vec<_>>();
        assert_eq!(tvec.len(), tp.len());
    }
}
