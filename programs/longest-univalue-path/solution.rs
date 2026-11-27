fn extend(t: &Tree, v: i64, down: i64) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(cv, _, _) => {
            if *cv == v {
                down + 1
            } else {
                0
            }
        }
    }
}

fn max_i64(a: i64, b: i64) -> i64 {
    if a > b {
        a
    } else {
        b
    }
}

fn univalue_dfs(t: &Tree) -> i64 {
    let base: i64 = 1000000;

    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let vv = *v;

            let lp = univalue_dfs(&**l);
            let rp = univalue_dfs(&**r);

            let ld = lp / base;
            let lb = lp % base;
            let rd = rp / base;
            let rb = rp % base;

            let llen = extend(&**l, vv, ld);
            let rlen = extend(&**r, vv, rd);

            let best0 = max_i64(lb, rb);
            let through = llen + rlen;
            let best = max_i64(best0, through);
            let down = max_i64(llen, rlen);

            down * base + best
        }
    }
}

pub fn longest_univalue_path(root: &Tree) -> i64 {
    let base: i64 = 1000000;
    let packed = univalue_dfs(root);
    packed % base
}
