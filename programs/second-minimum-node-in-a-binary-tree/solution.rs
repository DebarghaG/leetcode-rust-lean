pub fn find_second_minimum_value(root: &Tree) -> i64 {
    match root {
        Tree::Null => -1,
        Tree::Node(v, _, _) => {
            let minv = *v;
            dfs(root, minv, -1)
        }
    }
}

fn dfs(t: &Tree, minv: i64, mut best: i64) -> i64 {
    match t {
        Tree::Null => best,
        Tree::Node(v, left, right) => {
            let val = *v;
            if val > minv && (best == -1 || val < best) {
                best = val;
            }
            best = dfs(&**left, minv, best);
            best = dfs(&**right, minv, best);
            best
        }
    }
}
