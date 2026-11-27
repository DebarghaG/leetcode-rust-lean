const B: i64 = 1000000;

fn is_null(t: &Tree) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(_, _, _) => false,
    }
}

fn node_val(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, _, _) => *v,
    }
}

fn dfs(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let val = *v;
            let mut inc: i64 = 1;
            let mut dec: i64 = 1;
            let mut best: i64 = 1;

            let lref: &Tree = &**l;
            if !is_null(lref) {
                let lv = node_val(lref);
                let p = dfs(lref);
                let ldec = p % B;
                let mid = p / B;
                let linc = mid % B;
                let lbest = mid / B;
                if lv == val + 1 && linc + 1 > inc {
                    inc = linc + 1;
                }
                if lv == val - 1 && ldec + 1 > dec {
                    dec = ldec + 1;
                }
                if lbest > best {
                    best = lbest;
                }
            }

            let rref: &Tree = &**r;
            if !is_null(rref) {
                let rv = node_val(rref);
                let p = dfs(rref);
                let rdec = p % B;
                let mid = p / B;
                let rinc = mid % B;
                let rbest = mid / B;
                if rv == val + 1 && rinc + 1 > inc {
                    inc = rinc + 1;
                }
                if rv == val - 1 && rdec + 1 > dec {
                    dec = rdec + 1;
                }
                if rbest > best {
                    best = rbest;
                }
            }

            let cand = inc + dec - 1;
            if cand > best {
                best = cand;
            }

            (best * B + inc) * B + dec
        }
    }
}

pub fn longest_consecutive(root: &Tree) -> i64 {
    let p = dfs(root);
    p / (B * B)
}
