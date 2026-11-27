fn excess(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let left_excess = excess(&**l);
            let right_excess = excess(&**r);
            *v - 1 + left_excess + right_excess
        }
    }
}

fn abs_val(x: i64) -> i64 {
    if x < 0 {
        0 - x
    } else {
        x
    }
}

fn total_moves(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, r) => {
            let left_moves = total_moves(&**l);
            let right_moves = total_moves(&**r);

            let left_excess = excess(&**l);
            let right_excess = excess(&**r);

            left_moves + right_moves + abs_val(left_excess) + abs_val(right_excess)
        }
    }
}

pub fn distribute_coins(root: &Tree) -> i64 {
    total_moves(root)
}
