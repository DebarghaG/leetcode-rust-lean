pub fn largest_values(root: &Tree) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    dfs(root, 0, &mut out);
    out
}

fn dfs(t: &Tree, depth: usize, out: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            if depth == out.len() {
                out.push(*v);
            } else if *v > out[depth] {
                out[depth] = *v;
            }

            dfs(&**l, depth + 1, out);
            dfs(&**r, depth + 1, out);
        }
    }
}
