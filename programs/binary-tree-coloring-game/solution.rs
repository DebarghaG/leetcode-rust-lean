fn size(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, r) => 1 + size(l) + size(r),
    }
}

fn left_size_at(t: &Tree, x: i64) -> i64 {
    match t {
        Tree::Null => -1,
        Tree::Node(v, l, r) => {
            if *v == x {
                size(l)
            } else {
                let a = left_size_at(l, x);
                if a >= 0 {
                    a
                } else {
                    left_size_at(r, x)
                }
            }
        }
    }
}

fn right_size_at(t: &Tree, x: i64) -> i64 {
    match t {
        Tree::Null => -1,
        Tree::Node(v, l, r) => {
            if *v == x {
                size(r)
            } else {
                let a = right_size_at(l, x);
                if a >= 0 {
                    a
                } else {
                    right_size_at(r, x)
                }
            }
        }
    }
}

pub fn btree_game_winning_move(root: &Tree, n: i64, x: i64) -> bool {
    let left = left_size_at(root, x);
    let right = right_size_at(root, x);

    if left < 0 || right < 0 {
        return false;
    }

    let parent_side = n - 1 - left - right;

    let mut best = left;
    if right > best {
        best = right;
    }
    if parent_side > best {
        best = parent_side;
    }

    best * 2 > n
}
