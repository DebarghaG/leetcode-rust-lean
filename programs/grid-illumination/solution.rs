fn lower_bound(a: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = a.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

// Manual iterative bottom-up merge sort (avoids std `sort` machinery).
fn merge_sort(a: &mut Vec<i64>) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let mut buf: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        buf.push(0);
        t += 1;
    }
    let mut width: usize = 1;
    while width < n {
        let mut lo: usize = 0;
        while lo < n {
            let mut mid: usize = lo + width;
            if mid > n {
                mid = n;
            }
            let mut hi: usize = lo + 2 * width;
            if hi > n {
                hi = n;
            }
            let mut p: usize = lo;
            let mut q: usize = mid;
            let mut k: usize = lo;
            while p < mid && q < hi {
                if a[p] <= a[q] {
                    buf[k] = a[p];
                    p += 1;
                } else {
                    buf[k] = a[q];
                    q += 1;
                }
                k += 1;
            }
            while p < mid {
                buf[k] = a[p];
                p += 1;
                k += 1;
            }
            while q < hi {
                buf[k] = a[q];
                q += 1;
                k += 1;
            }
            lo = hi;
        }
        let mut s: usize = 0;
        while s < n {
            a[s] = buf[s];
            s += 1;
        }
        width = width * 2;
    }
}

// Given a sorted vector, build the vector of distinct values in order.
fn unique_sorted(a: &[i64]) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        if i == 0 || a[i] != a[i - 1] {
            out.push(a[i]);
        }
        i += 1;
    }
    out
}

pub fn grid_illumination(n: i64, lamps: &[Vec<i64>], queries: &[Vec<i64>]) -> Vec<i64> {
    let m = lamps.len();

    // Encode each lamp as id = row * n + col, then sort and dedup.
    let mut ids: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        let r = lamps[i][0];
        let c = lamps[i][1];
        ids.push(r * n + c);
        i += 1;
    }
    merge_sort(&mut ids);
    let uniq: Vec<i64> = unique_sorted(&ids);
    let l = uniq.len();

    // 1 means the lamp is still on.
    let mut active: Vec<i64> = Vec::new();
    i = 0;
    while i < l {
        active.push(1);
        i += 1;
    }

    // Collect the coordinates / diagonals that actually appear.
    let mut rv: Vec<i64> = Vec::new();
    let mut cv: Vec<i64> = Vec::new();
    let mut d1v: Vec<i64> = Vec::new();
    let mut d2v: Vec<i64> = Vec::new();
    i = 0;
    while i < l {
        let r = uniq[i] / n;
        let c = uniq[i] % n;
        rv.push(r);
        cv.push(c);
        d1v.push(r - c);
        d2v.push(r + c);
        i += 1;
    }
    merge_sort(&mut rv);
    merge_sort(&mut cv);
    merge_sort(&mut d1v);
    merge_sort(&mut d2v);
    let rows = unique_sorted(&rv);
    let cols = unique_sorted(&cv);
    let diag1 = unique_sorted(&d1v);
    let diag2 = unique_sorted(&d2v);

    // Counters of active lamps per compressed row / column / diagonal.
    let mut row_cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < rows.len() {
        row_cnt.push(0);
        i += 1;
    }
    let mut col_cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < cols.len() {
        col_cnt.push(0);
        i += 1;
    }
    let mut diag1_cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < diag1.len() {
        diag1_cnt.push(0);
        i += 1;
    }
    let mut diag2_cnt: Vec<i64> = Vec::new();
    i = 0;
    while i < diag2.len() {
        diag2_cnt.push(0);
        i += 1;
    }

    i = 0;
    while i < l {
        let r = uniq[i] / n;
        let c = uniq[i] % n;

        let ri = lower_bound(&rows, r);
        if ri < rows.len() && rows[ri] == r {
            row_cnt[ri] += 1;
        }
        let ci = lower_bound(&cols, c);
        if ci < cols.len() && cols[ci] == c {
            col_cnt[ci] += 1;
        }
        let d1 = r - c;
        let d1i = lower_bound(&diag1, d1);
        if d1i < diag1.len() && diag1[d1i] == d1 {
            diag1_cnt[d1i] += 1;
        }
        let d2 = r + c;
        let d2i = lower_bound(&diag2, d2);
        if d2i < diag2.len() && diag2[d2i] == d2 {
            diag2_cnt[d2i] += 1;
        }
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let qn = queries.len();
    let mut qi: usize = 0;

    while qi < qn {
        let qr = queries[qi][0];
        let qc = queries[qi][1];

        let mut lit: i64 = 0;

        let ri = lower_bound(&rows, qr);
        if ri < rows.len() && rows[ri] == qr && row_cnt[ri] > 0 {
            lit = 1;
        }
        let ci = lower_bound(&cols, qc);
        if ci < cols.len() && cols[ci] == qc && col_cnt[ci] > 0 {
            lit = 1;
        }
        let d1 = qr - qc;
        let d1i = lower_bound(&diag1, d1);
        if d1i < diag1.len() && diag1[d1i] == d1 && diag1_cnt[d1i] > 0 {
            lit = 1;
        }
        let d2 = qr + qc;
        let d2i = lower_bound(&diag2, d2);
        if d2i < diag2.len() && diag2[d2i] == d2 && diag2_cnt[d2i] > 0 {
            lit = 1;
        }

        ans.push(lit);

        // Turn off the lamp at the query cell and its 8 neighbors.
        let mut dr: i64 = -1;
        while dr <= 1 {
            let mut dc: i64 = -1;
            while dc <= 1 {
                let rr = qr + dr;
                let cc = qc + dc;

                if rr >= 0 && rr < n && cc >= 0 && cc < n {
                    let id = rr * n + cc;
                    let p = lower_bound(&uniq, id);

                    if p < l && uniq[p] == id && active[p] == 1 {
                        active[p] = 0;

                        let rri = lower_bound(&rows, rr);
                        if rri < rows.len() && rows[rri] == rr && row_cnt[rri] > 0 {
                            row_cnt[rri] -= 1;
                        }
                        let cci = lower_bound(&cols, cc);
                        if cci < cols.len() && cols[cci] == cc && col_cnt[cci] > 0 {
                            col_cnt[cci] -= 1;
                        }
                        let dd1 = rr - cc;
                        let dd1i = lower_bound(&diag1, dd1);
                        if dd1i < diag1.len() && diag1[dd1i] == dd1 && diag1_cnt[dd1i] > 0 {
                            diag1_cnt[dd1i] -= 1;
                        }
                        let dd2 = rr + cc;
                        let dd2i = lower_bound(&diag2, dd2);
                        if dd2i < diag2.len() && diag2[dd2i] == dd2 && diag2_cnt[dd2i] > 0 {
                            diag2_cnt[dd2i] -= 1;
                        }
                    }
                }

                dc += 1;
            }
            dr += 1;
        }

        qi += 1;
    }

    ans
}
