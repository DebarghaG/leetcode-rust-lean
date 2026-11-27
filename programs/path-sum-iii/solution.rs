fn count_down(node: &Tree, target: i64, acc: i64) -> i64 {
    match node {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let s = acc + *v;
            let mut cnt: i64 = 0;

            if s == target {
                cnt = cnt + 1;
            }

            cnt = cnt + count_down(&**l, target, s);
            cnt = cnt + count_down(&**r, target, s);

            cnt
        }
    }
}

fn all_paths(node: &Tree, target: i64) -> i64 {
    match node {
        Tree::Null => 0,
        Tree::Node(_, l, r) => {
            let mut ans: i64 = count_down(node, target, 0);
            ans = ans + all_paths(&**l, target);
            ans = ans + all_paths(&**r, target);
            ans
        }
    }
}

pub fn path_sum(root: &Tree, targetSum: i64) -> i64 {
    all_paths(root, targetSum)
}
