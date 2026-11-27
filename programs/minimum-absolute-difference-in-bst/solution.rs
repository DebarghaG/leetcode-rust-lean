fn collect_inorder(t: &Tree) -> Vec<i64> {
    match t {
        Tree::Null => Vec::new(),
        Tree::Node(v, l, r) => {
            let mut result: Vec<i64> = collect_inorder(&**l);
            result.push(*v);
            let rv: Vec<i64> = collect_inorder(&**r);
            let mut i: usize = 0;
            while i < rv.len() {
                result.push(rv[i]);
                i += 1;
            }
            result
        }
    }
}

pub fn get_minimum_difference(root: &Tree) -> i64 {
    let vals: Vec<i64> = collect_inorder(root);

    let mut best: i64 = 1000000000;
    let mut i: usize = 1;
    while i < vals.len() {
        let diff: i64 = vals[i] - vals[i - 1];
        if diff < best {
            best = diff;
        }
        i += 1;
    }

    best
}
