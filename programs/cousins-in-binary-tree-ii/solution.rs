fn collect_depth_sums(t: &Tree, depth: usize, sums: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            while sums.len() <= depth {
                sums.push(0);
            }
            sums[depth] = sums[depth] + *v;

            collect_depth_sums(&**l, depth + 1, sums);
            collect_depth_sums(&**r, depth + 1, sums);
        }
    }
}

fn build_replaced_tree(t: &Tree, depth: usize, sibling_group_sum: i64, sums: &[i64]) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, l, r) => {
            let mut new_value: i64 = 0;

            if depth > 0 {
                new_value = sums[depth] - sibling_group_sum;
            }

            let mut children_sum: i64 = 0;

            match &**l {
                Tree::Null => {}
                Tree::Node(lv, _, _) => {
                    children_sum = children_sum + *lv;
                }
            }

            match &**r {
                Tree::Null => {}
                Tree::Node(rv, _, _) => {
                    children_sum = children_sum + *rv;
                }
            }

            let new_left = build_replaced_tree(&**l, depth + 1, children_sum, sums);
            let new_right = build_replaced_tree(&**r, depth + 1, children_sum, sums);

            Tree::Node(new_value, Box::new(new_left), Box::new(new_right))
        }
    }
}

pub fn replace_value_in_tree(root: &Tree) -> Tree {
    let mut sums: Vec<i64> = Vec::new();
    collect_depth_sums(root, 0, &mut sums);
    build_replaced_tree(root, 0, 0, &sums)
}
