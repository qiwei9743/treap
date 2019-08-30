struct Node<T> {
    key: T,
    size: usize,
    priority: u64,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

impl<T: Ord> Node<T> {
    pub fn insert_or_replace(
        root: &mut Option<Box<Node<T>>>,
        new_node: Box<Node<T>>,
    ) -> Option<Box<Node<T>>> {
        // TODO:
        if let Some(ref mut root) = *root {
            root.insert(new_node)
        } else {
            *root = Some(new_node);
            None
        }
    }

    pub fn insert(&mut self, new_node: Box<Node<T>>) -> Option<Box<Node<T>>> {
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
            },
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

    pub fn nth(&self, nth: usize) -> Option<&T> {
        if nth >= self.size {
            return None;
        }

        let left_size = self.left.as_ref().map(|x| x.size).unwrap_or(0);
        if nth < left_size {
            self.left.as_ref().unwrap().nth(nth)
        } else if nth == left_size {
            Some(&self.key)
        } else {
            self.right.as_ref().unwrap().nth(nth - left_size - 1)
        }
    }

    fn rotate_left(&mut self) {
        let right = self.right.take();
        if let Some(mut node) = right {
            self.right = node.left.take();

            self.size -= node.size;
            node.size += self.size;
            self.size += self.right
                .as_ref()
                .map(|x| x.size)
                .unwrap_or(0);

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
            self.size += self.left
                .as_ref()
                .map(|x| x.size)
                .unwrap_or(0);

            let old_root = std::mem::replace(self, *node);
            self.right = Some(Box::new(old_root));
        }
    }
}

pub struct Treap<T>(Option<Box<Node<T>>>);

impl<T: Ord> Treap<T> {
    pub fn new() -> Treap<T> {
        Treap(None)
    }

    pub fn insert(&mut self, key: T) -> Option<T> {
        let new_node = Box::new(Node {
            key,
            size: 1,
            priority: rand::random(),
            left: None,
            right: None,
        });
        Node::insert_or_replace(&mut self.0, new_node).map(|x| x.key)
    }

    pub fn nth(&mut self, nth: usize) -> Option<&T> {
        if self.0.is_none() {
            return None
        }
        self.0.as_ref().unwrap().nth(nth)
    }
}

#[cfg(test)]
mod test {
    use super::Treap;
    #[test]
    fn test1() {
        let mut tp = Treap::new();
        tp.insert(10);
        tp.insert(11);
        tp.insert(13);
        assert_eq!(tp.nth(0), Some(&10));
        assert_eq!(tp.nth(1), Some(&11));
        assert_eq!(tp.nth(2), Some(&13));
    }
}
