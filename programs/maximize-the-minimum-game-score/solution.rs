fn feasible(points: &[i64], target: i64, m: i64) -> bool {
    if target <= 0 {
        return true;
    }
    let n = points.len();
    if n == 0 {
        return true;
    }
    if n == 1 {
        let need = (target + points[0] - 1) / points[0];
        return m >= 1 && need <= 1;
    }

    // Start: one move -1 -> 0, one visit to cell 0.
    let mut moves: i64 = 1;
    let mut visits: i64 = 1;
    let mut carry: i64 = 0; // pre-visits to current cell from round trips on previous cell
    let mut i: usize = 0;
    let mut ok: bool = true;
    let mut done: bool = false;

    while !done && ok {
        let p = points[i];
        let need_i = (target + p - 1) / p;

        if visits < need_i {
            let deficit = need_i - visits;
            visits += deficit;
            moves += 2 * deficit; // each round trip i->i+1->i costs 2, pre-visits i+1
            carry = deficit;
        } else {
            carry = 0;
        }

        if moves > m {
            ok = false;
        } else if i == n - 1 {
            done = true;
        } else {
            let next = i + 1;
            let pn = points[next];
            let need_next = (target + pn - 1) / pn;
            if next == n - 1 && carry >= need_next {
                // last cell already satisfied by the round trips; no need to move.
                done = true;
            } else {
                moves += 1;
                visits = carry + 1;
                i = next;
            }
        }
    }

    ok
}

pub fn max_score(points: &[i64], m: i64) -> i64 {
    let n = points.len();

    let mut maxp: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if points[i] > maxp {
            maxp = points[i];
        }
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = maxp * m + 1;

    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        if feasible(points, mid, m) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    lo
}
