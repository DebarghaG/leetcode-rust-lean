const B: i64 = 100000;

fn upd(best: i64, pi: i64, qj: i64) -> i64 {
    if pi > 0 {
        if qj > 0 {
            let d: i64 = (pi - 1) + (qj - 1);
            if d > best {
                return d;
            }
        }
    }
    best
}

// All arithmetic lives here: no borrows into the tree, so no borrow-context
// mismatch across control flow.
fn combine(val: i64, lp_packed: i64, rp_packed: i64, p: i64, q: i64) -> i64 {
    let l_p: i64 = lp_packed % B;
    let l_t: i64 = lp_packed / B;
    let l_q: i64 = l_t % B;
    let l_g: i64 = l_t / B;

    let r_p: i64 = rp_packed % B;
    let r_t: i64 = rp_packed / B;
    let r_q: i64 = r_t % B;
    let r_g: i64 = r_t / B;

    let mut sp: i64 = 0;
    if val == p {
        sp = 1;
    }
    let mut sq: i64 = 0;
    if val == q {
        sq = 1;
    }

    // depths (encoded as depth + 1) measured from the current node
    let mut lp: i64 = 0;
    if l_p > 0 {
        lp = l_p + 1;
    }
    let mut lq: i64 = 0;
    if l_q > 0 {
        lq = l_q + 1;
    }
    let mut rp: i64 = 0;
    if r_p > 0 {
        rp = r_p + 1;
    }
    let mut rq: i64 = 0;
    if r_q > 0 {
        rq = r_q + 1;
    }

    // best distance between a p-node and a q-node in DIFFERENT parts
    let mut best: i64 = -1;
    best = upd(best, sp, lq);
    best = upd(best, sp, rq);
    best = upd(best, lp, sq);
    best = upd(best, lp, rq);
    best = upd(best, rp, sq);
    best = upd(best, rp, lq);

    let mut g: i64 = best;
    if l_g > 0 {
        let lg: i64 = l_g - 1;
        if lg > g {
            g = lg;
        }
    }
    if r_g > 0 {
        let rg: i64 = r_g - 1;
        if rg > g {
            g = rg;
        }
    }

    let mut out_p: i64 = sp;
    if lp > out_p {
        out_p = lp;
    }
    if rp > out_p {
        out_p = rp;
    }
    let mut out_q: i64 = sq;
    if lq > out_q {
        out_q = lq;
    }
    if rq > out_q {
        out_q = rq;
    }

    let mut g_store: i64 = 0;
    if g >= 0 {
        g_store = g + 1;
    }

    out_p + out_q * B + g_store * (B * B)
}

fn solve(t: &Tree, p: i64, q: i64) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let val: i64 = *v;
            let lp: i64 = solve(l, p, q);
            let rp: i64 = solve(r, p, q);
            combine(val, lp, rp, p, q)
        }
    }
}

pub fn find_distance(root: &Tree, p: i64, q: i64) -> i64 {
    if p == q {
        return 0;
    }
    let packed: i64 = solve(root, p, q);
    let g_store: i64 = packed / (B * B);
    let mut result: i64 = -1;
    if g_store > 0 {
        result = g_store - 1;
    }
    result
}
