pub fn is_valid_sequence(root: &Tree, arr: &[i64]) -> bool {
    if arr.len() == 0 {
        return false;
    }
    valid_from(root, arr, 0)
}

fn valid_from(node: &Tree, arr: &[i64], idx: usize) -> bool {
    if idx >= arr.len() {
        return false;
    }

    match node {
        Tree::Null => false,
        Tree::Node(v, left, right) => {
            if *v != arr[idx] {
                return false;
            }

            if idx + 1 == arr.len() {
                match &**left {
                    Tree::Null => match &**right {
                        Tree::Null => true,
                        Tree::Node(_, _, _) => false,
                    },
                    Tree::Node(_, _, _) => false,
                }
            } else {
                valid_from(&**left, arr, idx + 1) || valid_from(&**right, arr, idx + 1)
            }
        }
    }
}
