fn collect_leaves(t: &Tree, out: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, left, right) => {
            let left_is_null = match &**left {
                Tree::Null => true,
                Tree::Node(_, _, _) => false,
            };
            let right_is_null = match &**right {
                Tree::Null => true,
                Tree::Node(_, _, _) => false,
            };

            if left_is_null && right_is_null {
                out.push(*v);
            } else {
                collect_leaves(&**left, out);
                collect_leaves(&**right, out);
            }
        }
    }
}

pub fn leaf_similar(root1: &Tree, root2: &Tree) -> bool {
    let mut leaves1: Vec<i64> = Vec::new();
    let mut leaves2: Vec<i64> = Vec::new();

    collect_leaves(root1, &mut leaves1);
    collect_leaves(root2, &mut leaves2);

    if leaves1.len() != leaves2.len() {
        return false;
    }

    let mut i: usize = 0;
    while i < leaves1.len() {
        if leaves1[i] != leaves2[i] {
            return false;
        }
        i = i + 1;
    }

    true
}
