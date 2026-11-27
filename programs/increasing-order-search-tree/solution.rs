fn collect_inorder(t: &Tree) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            let left_vals = collect_inorder(l);
            let mut i: usize = 0;
            while i < left_vals.len() {
                out.push(left_vals[i]);
                i = i + 1;
            }

            out.push(*v);

            let right_vals = collect_inorder(r);
            let mut j: usize = 0;
            while j < right_vals.len() {
                out.push(right_vals[j]);
                j = j + 1;
            }
        }
    }
    out
}

fn build_from_sorted(vals: &[i64]) -> Tree {
    let mut result: Tree = Tree::Null;
    let mut i: usize = vals.len();

    while i > 0 {
        i = i - 1;
        let value = vals[i];
        result = Tree::Node(value, Box::new(Tree::Null), Box::new(result));
    }

    result
}

pub fn increasing_bst(root: &Tree) -> Tree {
    let vals = collect_inorder(root);
    build_from_sorted(&vals)
}
