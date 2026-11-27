fn find_in_post(postorder: &[i64], start: usize, end: usize, target: i64) -> usize {
    let mut i = start;
    while i < end {
        if postorder[i] == target {
            return i;
        }
        i += 1;
    }
    start
}

fn build_tree(
    preorder: &[i64],
    postorder: &[i64],
    pre_l: usize,
    pre_r: usize,
    post_l: usize,
    post_r: usize,
) -> Tree {
    if pre_l >= pre_r {
        return Tree::Null;
    }

    let root = preorder[pre_l];

    if pre_r - pre_l == 1 {
        return Tree::Node(root, Box::new(Tree::Null), Box::new(Tree::Null));
    }

    let left_root = preorder[pre_l + 1];
    let left_root_post = find_in_post(postorder, post_l, post_r, left_root);
    let left_size = left_root_post - post_l + 1;

    let left = build_tree(
        preorder,
        postorder,
        pre_l + 1,
        pre_l + 1 + left_size,
        post_l,
        left_root_post + 1,
    );

    let right = build_tree(
        preorder,
        postorder,
        pre_l + 1 + left_size,
        pre_r,
        left_root_post + 1,
        post_r - 1,
    );

    Tree::Node(root, Box::new(left), Box::new(right))
}

pub fn construct_from_pre_post(preorder: &[i64], postorder: &[i64]) -> Tree {
    let n = preorder.len();
    build_tree(preorder, postorder, 0, n, 0, n)
}
