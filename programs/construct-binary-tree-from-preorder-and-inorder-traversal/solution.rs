pub fn build_tree(preorder: &[i64], inorder: &[i64]) -> Tree {
    let n = preorder.len();
    build_range(preorder, inorder, 0, n, 0, n, n)
}

fn build_range(
    preorder: &[i64],
    inorder: &[i64],
    pre_l: usize,
    pre_r: usize,
    in_l: usize,
    in_r: usize,
    fuel: usize,
) -> Tree {
    if fuel == 0 {
        return Tree::Null;
    }
    if pre_l >= pre_r {
        return Tree::Null;
    }
    if in_l >= in_r {
        return Tree::Null;
    }

    let root_val = preorder[pre_l];

    let mut root_pos = in_l;
    let mut found = false;
    let mut i = in_l;

    while i < in_r {
        if inorder[i] == root_val {
            root_pos = i;
            found = true;
        }
        i += 1;
    }

    if !found {
        return Tree::Null;
    }

    let left_len = root_pos - in_l;

    let left = build_range(
        preorder,
        inorder,
        pre_l + 1,
        pre_l + 1 + left_len,
        in_l,
        root_pos,
        fuel - 1,
    );

    let right = build_range(
        preorder,
        inorder,
        pre_l + 1 + left_len,
        pre_r,
        root_pos + 1,
        in_r,
        fuel - 1,
    );

    Tree::Node(root_val, Box::new(left), Box::new(right))
}
