const NEG: i64 = -1_000_000_000_000;

fn max_i64(a: i64, b: i64) -> i64 {
    if a >= b {
        a
    } else {
        b
    }
}

fn positive(x: i64) -> i64 {
    if x > 0 {
        x
    } else {
        0
    }
}

fn gain(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let vv: i64 = *v;
            let gl: i64 = gain(&**l);
            let gr: i64 = gain(&**r);
            let best_child: i64 = max_i64(gl, gr);
            vv + positive(best_child)
        }
    }
}

fn best(t: &Tree) -> i64 {
    match t {
        Tree::Null => NEG,
        Tree::Node(v, l, r) => {
            let vv: i64 = *v;
            let gl: i64 = gain(&**l);
            let gr: i64 = gain(&**r);
            let through: i64 = vv + positive(gl) + positive(gr);
            let bl: i64 = best(&**l);
            let br: i64 = best(&**r);
            let child_best: i64 = max_i64(bl, br);
            max_i64(through, child_best)
        }
    }
}

pub fn max_path_sum(root: &Tree) -> i64 {
    best(root)
}
