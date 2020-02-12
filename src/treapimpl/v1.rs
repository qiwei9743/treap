use rand::prelude::*;
use std::cell::{Ref, RefCell};
use std::rc::{Rc, Weak};

#[derive(Debug)]
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
    T: Ord + std::fmt::Debug,
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
        let rkey = &key;
        if let Some(rc_root) = root.clone().as_ref() {
            let cmp = rkey.cmp(&rc_root.as_ref().borrow().key);
            let inserted = match cmp {
                std::cmp::Ordering::Less => {
                    let ret =
                        Self::_insert(Some(rc_root.clone()), &mut rc_root.borrow_mut().left, key);
                    if rc_root.as_ref().borrow().priority
                        < rc_root
                            .borrow()
                            .left
                            .as_ref()
                            .map_or(0, |x| x.as_ref().borrow().priority)
                    {
                        Self::rotate_right(root);
                    }
                    ret
                }
                std::cmp::Ordering::Greater => {
                    let ret =
                        Self::_insert(Some(rc_root.clone()), &mut rc_root.borrow_mut().right, key);
                    if rc_root.borrow().priority
                        < rc_root
                            .borrow()
                            .right
                            .as_ref()
                            .map_or(0, |x| x.as_ref().borrow().priority)
                    {
                        Self::rotate_left(root);
                    }
                    ret
                }
                std::cmp::Ordering::Equal => false,
            };

            if inserted {
                rc_root.borrow_mut().size += 1;
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
    // fn nth(&self, root: Option<Rc<RefCell<TNode<T>>>>, nth: usize) -> Option<Ref<T>> {
    //     if nth < root.as_ref().map(|x| x.borrow().size).unwrap_or(0) {
    //         let left_size = root
    //             .as_ref()
    //             .and_then(|x| x.borrow().left.as_ref().map(|y| y.borrow().size))
    //             .unwrap_or(0);

    //         return if nth < left_size {
    //             self.nth(
    //                 root.as_ref().unwrap().borrow().left.clone(),
    //                 nth
    //             )
    //         } else if nth == left_size {
    //             root.clone().map(|x| Ref::map(x.borrow(), |y| &y.key))
    //         } else {
    //             self.nth(
    //                 root.as_ref().unwrap().borrow().right.clone(),
    //                 nth - left_size - 1
    //             )
    //         }
    //     }
    //     None
    // }

    // fn nth(root: &Option<Rc<RefCell<TNode<T>>>>, nth: usize) -> Option<Ref<T>> {
    //     if nth < root.as_ref().map(|x| x.borrow().size).unwrap_or(0) {
    //         let left_size = root
    //             .as_ref()
    //             .and_then(|x| x.borrow().left.as_ref().map(|y| y.borrow().size))
    //             .unwrap_or(0);

    //         return if nth < left_size {
    //             Self::nth(&root.as_ref().unwrap().borrow().left, nth)
    //         } else if nth == left_size {
    //             root.as_ref().map(|x| Ref::map(x.borrow(), |y| &y.key))
    //         } else {
    //             Self::nth(&root.as_ref().unwrap().borrow().right, nth - left_size - 1)
    //         }
    //     }
    //     None
    // }

    // fn nth(&self, nth: usize) -> Option<&T> {
    // fn nth(&self, nth: usize) -> Option<Ref<T>> {
    // fn nth(&self, nth: usize) -> Option<Rc<RefCell<TNode<T>>>> {
    //     let root = self.0.clone();
    //     let node = Self::_nth(root, nth);
    //     node
    // }

    // fn _nth(root: Option<Rc<RefCell<TNode<T>>>>, nth: usize) -> Option<Rc<RefCell<TNode<T>>>> {
    //     if nth < root.as_ref().map(|x| x.borrow().size).unwrap_or(0) {
    //         let left_size = root
    //             .as_ref()
    //             .and_then(|x| x.borrow().left.as_ref().map(|y| y.borrow().size))
    //             .unwrap_or(0);
    //         return if nth < left_size {
    //             Self::_nth(root.as_ref().unwrap().borrow().left.clone(), nth)
    //         } else if nth == left_size {
    //             root
    //         } else {
    //             Self::_nth(root.as_ref().unwrap().borrow().right.clone(), nth - left_size - 1)
    //         };
    //     }
    //     None
    // }

    fn find_nth(root: &Option<Rc<RefCell<TNode<T>>>>, nth: usize) -> Option<Rc<RefCell<TNode<T>>>> {
        if let Some(rc_root) = root.as_ref() {
            let left_cnt = if let Some(left) = rc_root.borrow().left.as_ref() {
                let left_node = left.as_ref().borrow();
                if left_node.size < nth {
                    return Self::find_nth(&rc_root.borrow().right, nth - left_node.size);
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

    fn find(root: &Option<Rc<RefCell<TNode<T>>>>, key: &T) -> Option<Rc<RefCell<TNode<T>>>> {
        if let Some(rc_root) = root.as_ref() {
            match key.cmp(&rc_root.borrow().key) {
                std::cmp::Ordering::Less => Self::find(&rc_root.borrow().left, key),
                std::cmp::Ordering::Greater => Self::find(&rc_root.borrow().right, key),
                std::cmp::Ordering::Equal => Some(rc_root.clone()),
            }
        } else {
            None
        }
    }
    pub fn delete(key: T) {
    }

    fn delete_nth(nth: usize) -> Option<Rc<RefCell<TNode<T>>>> {
        unimplemented!()
    }
    fn _delete(node: Rc<RefCell<TNode<T>>>) {}
    fn rotate_left(root: &mut Option<Rc<RefCell<TNode<T>>>>) {
        let right = root.as_ref().unwrap().borrow_mut().right.take();
        if right.is_none() {
            return;
        }
        root.as_ref().unwrap().borrow_mut().right =
            right.as_ref().unwrap().borrow_mut().left.take();
        right.as_ref().unwrap().borrow_mut().parent = root
            .as_ref()
            .unwrap()
            .borrow_mut()
            .parent
            .upgrade()
            .map_or(Weak::new(), |x| Rc::downgrade(&x));

        root.as_ref().unwrap().borrow_mut().parent = Rc::downgrade(right.as_ref().unwrap());
        right.as_ref().unwrap().borrow_mut().left = root.take();

        *root = right;
    }
    fn rotate_right(root: &mut Option<Rc<RefCell<TNode<T>>>>) {
        let left = root.as_ref().unwrap().borrow_mut().left.take();
        if left.is_none() {
            return;
        }
        root.as_ref().unwrap().borrow_mut().left = left.as_ref().unwrap().borrow_mut().right.take();
        left.as_ref().unwrap().borrow_mut().parent = root
            .as_ref()
            .unwrap()
            .borrow_mut()
            .parent
            .upgrade()
            .map_or(Weak::new(), |x| Rc::downgrade(&x));
        root.as_ref().unwrap().borrow_mut().parent = Rc::downgrade(left.as_ref().unwrap());
        left.as_ref().unwrap().borrow_mut().right = root.take();
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
                let root = &dq.pop_front().unwrap();
                println!("{:?}", root);

                if let Some(node) = root.borrow().left.as_ref() {
                    dq.push_back(node.clone());
                };
                if let Some(node) = root.borrow().right.as_ref() {
                    dq.push_back(node.clone());
                };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        let mut treap = Treap::new();
        treap.insert(10);
        treap.insert(12);
        treap.insert(13);

        treap.bfs_print();
    }
}
