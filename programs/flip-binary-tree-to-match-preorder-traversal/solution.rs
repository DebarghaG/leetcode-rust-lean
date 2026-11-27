pub fn flip_match_voyage(root: &Tree, voyage: &[i64]) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let mut idx: usize = 0;

    let ok = dfs_flip(root, voyage, &mut idx, &mut ans);

    if ok && idx == voyage.len() {
        ans
    } else {
        let mut bad: Vec<i64> = Vec::new();
        bad.push(-1);
        bad
    }
}

fn dfs_flip(t: &Tree, voyage: &[i64], idx: &mut usize, ans: &mut Vec<i64>) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(v, left, right) => {
            if *idx >= voyage.len() {
                return false;
            }
            if voyage[*idx] != *v {
                return false;
            }
            *idx = *idx + 1;

            let has_left = match &**left {
                Tree::Null => false,
                Tree::Node(_, _, _) => true,
            };
            let has_right = match &**right {
                Tree::Null => false,
                Tree::Node(_, _, _) => true,
            };

            if has_left && has_right {
                if *idx >= voyage.len() {
                    return false;
                }

                let next = voyage[*idx];
                let left_val = match &**left {
                    Tree::Node(lv, _, _) => *lv,
                    Tree::Null => 0,
                };

                if left_val == next {
                    if !dfs_flip(&**left, voyage, idx, ans) {
                        return false;
                    }
                    if !dfs_flip(&**right, voyage, idx, ans) {
                        return false;
                    }
                    true
                } else {
                    let right_val = match &**right {
                        Tree::Node(rv, _, _) => *rv,
                        Tree::Null => 0,
                    };

                    if right_val == next {
                        ans.push(*v);
                        if !dfs_flip(&**right, voyage, idx, ans) {
                            return false;
                        }
                        if !dfs_flip(&**left, voyage, idx, ans) {
                            return false;
                        }
                        true
                    } else {
                        false
                    }
                }
            } else if has_left {
                dfs_flip(&**left, voyage, idx, ans)
            } else if has_right {
                dfs_flip(&**right, voyage, idx, ans)
            } else {
                true
            }
        }
    }
}
