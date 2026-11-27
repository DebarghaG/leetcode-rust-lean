fn dfs(node: &Tree, prev: i64, has_prev: bool, prev_len: i64) -> i64 {
    match node {
        Tree::Null => 0,
        Tree::Node(v, left, right) => {
            let val = *v;
            let mut cur = 1;

            if has_prev && val == prev + 1 {
                cur = prev_len + 1;
            }

            let left_ref: &Tree = &**left;
            let right_ref: &Tree = &**right;

            let left_best = dfs(left_ref, val, true, cur);
            let right_best = dfs(right_ref, val, true, cur);

            let mut best = cur;
            if left_best > best {
                best = left_best;
            }
            if right_best > best {
                best = right_best;
            }

            best
        }
    }
}

pub fn longest_consecutive(root: &Tree) -> i64 {
    dfs(root, 0, false, 0)
}
