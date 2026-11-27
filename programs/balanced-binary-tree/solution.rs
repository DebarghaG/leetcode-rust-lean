fn imax(a: i64, b: i64) -> i64 {
    let mut r: i64 = a;
    if b > a {
        r = b;
    }
    r
}

fn iabs(a: i64) -> i64 {
    let mut r: i64 = a;
    if a < 0 {
        r = 0 - a;
    }
    r
}

fn combine(lh: i64, rh: i64) -> i64 {
    if lh < 0 {
        return -1;
    }
    if rh < 0 {
        return -1;
    }
    let diff = lh - rh;
    let adiff = iabs(diff);
    if adiff > 1 {
        return -1;
    }
    imax(lh, rh) + 1
}

fn height(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            let lh = height(&**left);
            let rh = height(&**right);
            combine(lh, rh)
        }
    }
}

pub fn is_balanced(root: &Tree) -> bool {
    height(root) >= 0
}
