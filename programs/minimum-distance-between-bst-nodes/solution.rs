fn collect_inorder(t: &Tree) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();

    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            let left = collect_inorder(&**l);
            let mut i: usize = 0;
            while i < left.len() {
                out.push(left[i]);
                i += 1;
            }

            out.push(*v);

            let right = collect_inorder(&**r);
            let mut j: usize = 0;
            while j < right.len() {
                out.push(right[j]);
                j += 1;
            }
        }
    }

    out
}

pub fn min_diff_in_bst(root: &Tree) -> i64 {
    let vals = collect_inorder(root);

    if vals.len() < 2 {
        return 0;
    }

    let mut ans: i64 = 1000000000;
    let mut i: usize = 1;

    while i < vals.len() {
        let diff = vals[i] - vals[i - 1];
        if diff < ans {
            ans = diff;
        }
        i += 1;
    }

    ans
}
