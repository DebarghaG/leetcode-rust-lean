fn check_tree(
    t: &Tree,
    level: usize,
    even_level: bool,
    prev: &mut Vec<i64>,
    seen: &mut Vec<bool>,
) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(vbox, left, right) => {
            let v = *vbox;

            while seen.len() <= level {
                prev.push(0);
                seen.push(false);
            }

            if even_level {
                if v % 2 == 0 {
                    return false;
                }
                if seen[level] {
                    if v <= prev[level] {
                        return false;
                    }
                }
            } else {
                if v % 2 != 0 {
                    return false;
                }
                if seen[level] {
                    if v >= prev[level] {
                        return false;
                    }
                }
            }

            prev[level] = v;
            seen[level] = true;

            if !check_tree(&**left, level + 1, !even_level, prev, seen) {
                return false;
            }

            check_tree(&**right, level + 1, !even_level, prev, seen)
        }
    }
}

pub fn is_even_odd_tree(root: &Tree) -> bool {
    let mut prev: Vec<i64> = Vec::new();
    let mut seen: Vec<bool> = Vec::new();
    check_tree(root, 0, true, &mut prev, &mut seen)
}
