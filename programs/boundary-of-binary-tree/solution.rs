fn is_leaf(t: &Tree) -> bool {
    match t {
        Tree::Null => false,
        Tree::Node(_, l, r) => {
            let left_null = match &**l {
                Tree::Null => true,
                _ => false,
            };
            let right_null = match &**r {
                Tree::Null => true,
                _ => false,
            };
            left_null && right_null
        }
    }
}

fn collect_leaves(t: &Tree) -> Vec<i64> {
    match t {
        Tree::Null => Vec::new(),
        Tree::Node(v, l, r) => {
            let left_null = match &**l {
                Tree::Null => true,
                _ => false,
            };
            let right_null = match &**r {
                Tree::Null => true,
                _ => false,
            };

            if left_null && right_null {
                let mut out: Vec<i64> = Vec::new();
                out.push(*v);
                out
            } else {
                let mut out: Vec<i64> = collect_leaves(&**l);
                let right_part: Vec<i64> = collect_leaves(&**r);

                let mut i: usize = 0;
                while i < right_part.len() {
                    out.push(right_part[i]);
                    i += 1;
                }

                out
            }
        }
    }
}

fn left_boundary(t: &Tree) -> Vec<i64> {
    match t {
        Tree::Null => Vec::new(),
        Tree::Node(v, l, r) => {
            if is_leaf(t) {
                Vec::new()
            } else {
                let mut out: Vec<i64> = Vec::new();
                out.push(*v);

                let l_null = match &**l {
                    Tree::Null => true,
                    _ => false,
                };

                let sub: Vec<i64> = if l_null {
                    left_boundary(&**r)
                } else {
                    left_boundary(&**l)
                };

                let mut i: usize = 0;
                while i < sub.len() {
                    out.push(sub[i]);
                    i += 1;
                }

                out
            }
        }
    }
}

fn right_boundary(t: &Tree) -> Vec<i64> {
    match t {
        Tree::Null => Vec::new(),
        Tree::Node(v, l, r) => {
            if is_leaf(t) {
                Vec::new()
            } else {
                let mut out: Vec<i64> = Vec::new();
                out.push(*v);

                let r_null = match &**r {
                    Tree::Null => true,
                    _ => false,
                };

                let sub: Vec<i64> = if r_null {
                    right_boundary(&**l)
                } else {
                    right_boundary(&**r)
                };

                let mut i: usize = 0;
                while i < sub.len() {
                    out.push(sub[i]);
                    i += 1;
                }

                out
            }
        }
    }
}

pub fn boundary_of_binary_tree(root: &Tree) -> Vec<i64> {
    let mut res: Vec<i64> = Vec::new();

    match root {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            res.push(*v);

            if !is_leaf(root) {
                // Left boundary: starts at root's left child, leaves excluded.
                let lb: Vec<i64> = left_boundary(&**l);
                let mut i: usize = 0;
                while i < lb.len() {
                    res.push(lb[i]);
                    i += 1;
                }

                // All leaves, left to right.
                let leaves: Vec<i64> = collect_leaves(root);
                let mut k: usize = 0;
                while k < leaves.len() {
                    res.push(leaves[k]);
                    k += 1;
                }

                // Right boundary: starts at root's right child, leaves excluded,
                // appended in reverse order.
                let rb: Vec<i64> = right_boundary(&**r);
                let mut j: usize = rb.len();
                while j > 0 {
                    j = j - 1;
                    res.push(rb[j]);
                }
            }
        }
    }

    res
}
