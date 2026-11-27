pub fn longest_zig_zag(root: &Tree) -> i64 {
    let code = dfs(root);
    code % 100000
}

fn dfs(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            let left_code = dfs(&**left);
            let right_code = dfs(&**right);

            let left_down = match &**left {
                Tree::Null => 0,
                Tree::Node(_, _, _) => 1 + (left_code / 100000) % 100000,
            };

            let right_down = match &**right {
                Tree::Null => 0,
                Tree::Node(_, _, _) => 1 + (right_code / 10000000000),
            };

            let mut best = left_down;
            if right_down > best {
                best = right_down;
            }

            let left_best = left_code % 100000;
            if left_best > best {
                best = left_best;
            }

            let right_best = right_code % 100000;
            if right_best > best {
                best = right_best;
            }

            left_down * 10000000000 + right_down * 100000 + best
        }
    }
}
