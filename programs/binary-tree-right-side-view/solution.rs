fn collect_right(t: &Tree, depth: usize, out: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(value, left, right) => {
            if depth == out.len() {
                out.push(*value);
            }
            collect_right(&**right, depth + 1, out);
            collect_right(&**left, depth + 1, out);
        }
    }
}

pub fn right_side_view(root: &Tree) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    collect_right(root, 0, &mut out);
    out
}
