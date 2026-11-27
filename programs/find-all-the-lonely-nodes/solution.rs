pub fn get_lonely_nodes(root: &Tree) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    collect_lonely(root, false, &mut result);
    result
}

fn collect_lonely(node: &Tree, is_lonely: bool, result: &mut Vec<i64>) {
    match node {
        Tree::Null => {}
        Tree::Node(value, left, right) => {
            if is_lonely {
                result.push(*value);
            }

            let l: &Tree = &**left;
            let r: &Tree = &**right;

            match (l, r) {
                (Tree::Null, Tree::Null) => {}
                (Tree::Null, Tree::Node(_, _, _)) => {
                    collect_lonely(r, true, result);
                }
                (Tree::Node(_, _, _), Tree::Null) => {
                    collect_lonely(l, true, result);
                }
                (Tree::Node(_, _, _), Tree::Node(_, _, _)) => {
                    collect_lonely(l, false, result);
                    collect_lonely(r, false, result);
                }
            }
        }
    }
}
