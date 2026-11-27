fn dfs(t: &Tree, mn: i64, mx: i64) -> i64 {
    match t {
        Tree::Null => mx - mn,
        Tree::Node(v, l, r) => {
            let val = *v;
            let nmn = if val < mn { val } else { mn };
            let nmx = if val > mx { val } else { mx };
            let a = dfs(l, nmn, nmx);
            let b = dfs(r, nmn, nmx);
            if a > b { a } else { b }
        }
    }
}

pub fn max_ancestor_diff(root: &Tree) -> i64 {
    match root {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let val = *v;
            let a = dfs(l, val, val);
            let b = dfs(r, val, val);
            if a > b { a } else { b }
        }
    }
}
