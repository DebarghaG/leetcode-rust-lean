fn depth_of(t: &Tree, target: i64) -> i64 {
    match t {
        Tree::Null => -1,
        Tree::Node(v, l, r) => {
            if *v == target {
                0
            } else {
                let dl = depth_of(&**l, target);
                if dl >= 0 {
                    dl + 1
                } else {
                    let dr = depth_of(&**r, target);
                    if dr >= 0 {
                        dr + 1
                    } else {
                        -1
                    }
                }
            }
        }
    }
}

fn parent_of(t: &Tree, target: i64, parent: i64) -> i64 {
    match t {
        Tree::Null => -1,
        Tree::Node(v, l, r) => {
            if *v == target {
                parent
            } else {
                let pl = parent_of(&**l, target, *v);
                if pl != -1 {
                    pl
                } else {
                    parent_of(&**r, target, *v)
                }
            }
        }
    }
}

pub fn is_cousins(root: &Tree, x: i64, y: i64) -> bool {
    let dx = depth_of(root, x);
    let dy = depth_of(root, y);

    if dx != dy {
        return false;
    }

    let px = parent_of(root, x, 0);
    let py = parent_of(root, y, 0);

    px != py
}
