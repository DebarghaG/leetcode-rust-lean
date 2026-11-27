fn left_height(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, _) => 1 + left_height(l),
    }
}

fn right_height(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, _, r) => 1 + right_height(r),
    }
}

fn perfect_nodes(h: i64) -> i64 {
    let mut res: i64 = 1;
    let mut i: i64 = 0;
    while i < h {
        res = res * 2;
        i = i + 1;
    }
    res - 1
}

fn count_impl(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, r) => {
            let lh = left_height(t);
            let rh = right_height(t);
            if lh == rh {
                perfect_nodes(lh)
            } else {
                1 + count_impl(l) + count_impl(r)
            }
        }
    }
}

pub fn count_nodes(root: &Tree) -> i64 {
    count_impl(root)
}
