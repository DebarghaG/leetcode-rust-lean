fn has_one(t: &Tree) -> bool {
    match t {
        Tree::Null => false,
        Tree::Node(v, l, r) => {
            if *v == 1 {
                true
            } else if has_one(&**l) {
                true
            } else {
                has_one(&**r)
            }
        }
    }
}

fn prune_impl(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, l, r) => {
            let keep = has_one(t);
            let nl = prune_impl(&**l);
            let nr = prune_impl(&**r);
            match keep {
                true => Tree::Node(*v, Box::new(nl), Box::new(nr)),
                false => Tree::Null,
            }
        }
    }
}

pub fn prune_tree(root: &Tree) -> Tree {
    prune_impl(root)
}
