use rand::prelude::*;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

#[derive(Debug)]
#[repr(C)]
struct TNode<T: std::fmt::Debug> {
    key: T,
    priority: u16,
    size: usize,
    left: Option<Rc<RefCell<TNode<T>>>>,
    right: Option<Rc<RefCell<TNode<T>>>>,
    parent: Weak<RefCell<TNode<T>>>,
}

pub struct Treap<T>(Option<Rc<RefCell<TNode<T>>>>)
where
    T: std::fmt::Debug;

impl<T> Treap<T>
where
    T: PartialOrd + Default + std::fmt::Debug,
{
    pub fn new() -> Treap<T> {
        println!("{:?}", std::mem::size_of::<TNode<i32>>());
        Treap(None)
    }
    pub fn insert(&mut self, key: T) {
        Self::_insert(None, &mut self.0, key);
    }
    fn _insert(
        parent: Option<Rc<RefCell<TNode<T>>>>,
        root: &mut Option<Rc<RefCell<TNode<T>>>>,
        key: T,
    ) -> bool {
        if let Some(rc_root) = root.clone() {
            let inserted = if key < rc_root.as_ref().borrow().key {
                let ret = Self::_insert(
                    Some(rc_root.clone()),
                    &mut rc_root.as_ref().borrow_mut().left,
                    key,
                );
                if rc_root.as_ref().borrow().priority
                    < rc_root
                        .as_ref()
                        .borrow()
                        .left
                        .as_ref()
                        .map_or(0, |x| x.as_ref().borrow().priority)
                {
                    Self::rotate_right(root);
                }
                ret
            } else if key > rc_root.as_ref().borrow().key {
                let ret = Self::_insert(
                    Some(rc_root.clone()),
                    &mut rc_root.as_ref().borrow_mut().right,
                    key,
                );
                if rc_root.as_ref().borrow().priority
                    < rc_root
                        .as_ref()
                        .borrow()
                        .right
                        .as_ref()
                        .map_or(0, |x| x.as_ref().borrow().priority)
                {
                    Self::rotate_left(root);
                }
                ret
            } else {
                false
            };

            if inserted {
                rc_root.as_ref().borrow_mut().size += 1;
            }
            inserted
        } else {
            *root = Some(Rc::new(RefCell::new(TNode {
                key,
                priority: random(),
                size: 1,
                left: None,
                right: None,
                parent: parent
                    .as_ref()
                    .map(|x| Rc::downgrade(x))
                    .unwrap_or(Weak::new()),
            })));
            true
        }
    }

    fn nth(root: Option<Rc<RefCell<TNode<T>>>>) -> Option<usize> {
        unimplemented!()
    }

    fn find_nth(root: &Option<Rc<RefCell<TNode<T>>>>, nth: usize) -> Option<Rc<RefCell<TNode<T>>>> {
        // 0, 1, 2, 3, 4
        if let Some(rc_root) = root {
            let left_cnt = if let Some(left) = rc_root.as_ref().borrow().left.as_ref() {
                let left_node = left.as_ref().borrow();
                if left_node.size < nth {
                    return Self::find_nth(&rc_root.as_ref().borrow().right, nth - left_node.size);
                } else if left_node.size > nth {
                    left_node.size
                } else {
                    return Some(rc_root.clone());
                }
            } else {
                0
            };
            return Self::find_nth(&rc_root.as_ref().borrow().right, nth - left_cnt - 1);
        }
        None
    }

    fn find(root: &Option<Rc<RefCell<TNode<T>>>>, key: T) -> Option<Rc<RefCell<TNode<T>>>> {
        if let Some(rc_root) = root {
            let root_node = rc_root.as_ref().borrow();
            if root_node.key < key {
                return Self::find(&root_node.left, key);
            } else if root_node.key > key {
                return Self::find(&root_node.right, key);
            } else {
                return Some(rc_root.clone());
            }
        }
        None
    }
    pub fn delete(key: T) {}

    fn delete_nth(nth: usize) -> Option<Rc<RefCell<TNode<T>>>> {
        unimplemented!()
    }
    fn _delete(node: Rc<RefCell<TNode<T>>>) {}
    fn rotate_left(root: &mut Option<Rc<RefCell<TNode<T>>>>) {
        // @right must not be a None
        let right = root.as_ref().unwrap().as_ref().borrow_mut().right.take();
        if right.is_none() {
            return;
        }
        root.as_ref().unwrap().as_ref().borrow_mut().right =
            right.as_ref().unwrap().as_ref().borrow_mut().left.take();
        right.as_ref().unwrap().as_ref().borrow_mut().parent = root
            .as_ref()
            .unwrap()
            .as_ref()
            .borrow_mut()
            .parent
            .upgrade()
            .map_or(Weak::new(), |x| Rc::downgrade(&x));
        root.as_ref().unwrap().as_ref().borrow_mut().parent =
            Rc::downgrade(right.as_ref().unwrap());
        right.as_ref().unwrap().as_ref().borrow_mut().left = root.take();

        *root = right;
    }
    fn rotate_right(root: &mut Option<Rc<RefCell<TNode<T>>>>) {
        // @left must not be a None
        let left = root.as_ref().unwrap().as_ref().borrow_mut().left.take();
        if left.is_none() {
            return;
        }
        root.as_ref().unwrap().as_ref().borrow_mut().left =
            left.as_ref().unwrap().as_ref().borrow_mut().right.take();
        left.as_ref().unwrap().as_ref().borrow_mut().parent = root
            .as_ref()
            .unwrap()
            .as_ref()
            .borrow_mut()
            .parent
            .upgrade()
            .map_or(Weak::new(), |x| Rc::downgrade(&x));
        root.as_ref().unwrap().as_ref().borrow_mut().parent = Rc::downgrade(left.as_ref().unwrap());
        left.as_ref().unwrap().as_ref().borrow_mut().right = root.take();
        *root = left;
    }
    pub fn bfs_print(&self) {
        let mut dq = std::collections::VecDeque::new();
        if self.0.is_none() {
            return;
        }
        dq.push_back(self.0.as_ref().unwrap().clone());
        while !dq.is_empty() {
            let cnt = dq.len();
            for _ in 0..cnt {
                let root = dq.pop_front().unwrap();
                println!("{:?}", root);

                if let Some(node) = root.as_ref().borrow().left.as_ref() {
                    dq.push_back(node.clone());
                };
                if let Some(node) = root.as_ref().borrow().right.as_ref() {
                    dq.push_back(node.clone());
                };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // use rand::prelude::*;

    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;
    #[test]
    fn test1() {
        let mut treap = Treap::new();
        treap.insert(10);
        treap.insert(12);
        treap.bfs_print();
    }
    #[test]
    fn test2() {
        let shared_map: Rc<RefCell<_>> = Rc::new(RefCell::new(HashMap::new()));
        shared_map.borrow_mut().insert("africa", 92388);
        shared_map.borrow_mut().insert("kyoto", 11837);
        shared_map.borrow_mut().insert("piccadilly", 11826);
        shared_map.borrow_mut().insert("marbles", 38);
    }
    #[test]
    fn test3() {
        let s1: Option<Rc<RefCell<_>>> = Some(Rc::new(RefCell::new(HashMap::new())));
        s1.as_ref().unwrap().borrow_mut().insert("africa", 92388);
        //        shared_map.borrow_mut().insert("kyoto", 11837);
        //        shared_map.borrow_mut().insert("piccadilly", 11826);
        //        shared_map.borrow_mut().insert("marbles", 38);
    }
}
