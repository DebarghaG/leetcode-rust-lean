pub fn max_product(root: &Tree) -> i64 {
    let total = sum_tree(root);
    let mut best: i64 = 0;
    traverse(root, total, &mut best, true);
    best % 1_000_000_007
}

fn sum_tree(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => *v + sum_tree(l) + sum_tree(r),
    }
}

fn traverse(t: &Tree, total: i64, best: &mut i64, is_root: bool) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let ls = traverse(l, total, best, false);
            let rs = traverse(r, total, best, false);
            let s = *v + ls + rs;
            if !is_root {
                let prod = s * (total - s);
                if prod > *best {
                    *best = prod;
                }
            }
            s
        }
    }
}
