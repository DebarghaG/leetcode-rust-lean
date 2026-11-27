fn matches(list: &List, tree: &Tree) -> bool {
    match list {
        List::Nil => true,
        List::Cons(v, next) => match tree {
            Tree::Null => false,
            Tree::Node(tv, left, right) => {
                if *v == *tv {
                    matches(&**next, &**left) || matches(&**next, &**right)
                } else {
                    false
                }
            }
        },
    }
}

fn search(list: &List, tree: &Tree) -> bool {
    match tree {
        Tree::Null => false,
        Tree::Node(_, left, right) => {
            if matches(list, tree) {
                true
            } else {
                search(list, &**left) || search(list, &**right)
            }
        }
    }
}

pub fn is_sub_path(head: &List, root: &Tree) -> bool {
    search(head, root)
}
