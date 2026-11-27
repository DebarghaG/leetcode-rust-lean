fn count_nodes(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => 1 + count_nodes(&**left) + count_nodes(&**right),
    }
}

fn flatten(
    t: &Tree,
    depth: i64,
    dep: &mut Vec<i64>,
    lc: &mut Vec<i64>,
    rc: &mut Vec<i64>,
    order: &mut Vec<i64>,
) {
    match t {
        Tree::Null => {}
        Tree::Node(v, left, right) => {
            let vv = *v;
            let idx = vv as usize;

            dep[idx] = depth;

            let lv: i64 = match &**left {
                Tree::Null => 0,
                Tree::Node(x, _, _) => *x,
            };
            let rv: i64 = match &**right {
                Tree::Null => 0,
                Tree::Node(x, _, _) => *x,
            };

            lc[idx] = lv;
            rc[idx] = rv;
            order.push(vv);

            flatten(&**left, depth + 1, dep, lc, rc, order);
            flatten(&**right, depth + 1, dep, lc, rc, order);
        }
    }
}

pub fn tree_queries(root: &Tree, queries: &[i64]) -> Vec<i64> {
    let n = count_nodes(root);
    let sz = (n + 1) as usize;

    let mut dep: Vec<i64> = Vec::new();
    let mut lc: Vec<i64> = Vec::new();
    let mut rc: Vec<i64> = Vec::new();
    let mut down: Vec<i64> = Vec::new();
    let mut out: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < sz {
        dep.push(0);
        lc.push(0);
        rc.push(0);
        down.push(0);
        out.push(0);
        i = i + 1;
    }

    let mut order: Vec<i64> = Vec::new();
    flatten(root, 0, &mut dep, &mut lc, &mut rc, &mut order);

    // Compute, for each node, the maximum absolute depth inside its subtree.
    let mut k: usize = order.len();
    while k > 0 {
        k = k - 1;
        let v = order[k];
        let idx = v as usize;

        let mut md = dep[idx];

        let l = lc[idx];
        if l != 0 {
            let li = l as usize;
            if down[li] > md {
                md = down[li];
            }
        }

        let r = rc[idx];
        if r != 0 {
            let ri = r as usize;
            if down[ri] > md {
                md = down[ri];
            }
        }

        down[idx] = md;
    }

    // Compute, for each node, the maximum absolute depth outside its subtree.
    let root_val: i64 = match root {
        Tree::Null => 0,
        Tree::Node(v, _, _) => *v,
    };

    if root_val != 0 {
        out[root_val as usize] = 0;
    }

    let mut p: usize = 0;
    let n_ord = order.len();
    while p < n_ord {
        let v = order[p];
        let idx = v as usize;

        let b = out[idx];
        let dv = dep[idx];
        let l = lc[idx];
        let r = rc[idx];

        if l != 0 {
            let li = l as usize;
            let mut nb = b;

            if dv > nb {
                nb = dv;
            }

            if r != 0 {
                let ri = r as usize;
                if down[ri] > nb {
                    nb = down[ri];
                }
            }

            out[li] = nb;
        }

        if r != 0 {
            let ri = r as usize;
            let mut nb = b;

            if dv > nb {
                nb = dv;
            }

            if l != 0 {
                let li = l as usize;
                if down[li] > nb {
                    nb = down[li];
                }
            }

            out[ri] = nb;
        }

        p = p + 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let m = queries.len();
    let mut j: usize = 0;
    while j < m {
        let q = queries[j];
        ans.push(out[q as usize]);
        j = j + 1;
    }

    ans
}
