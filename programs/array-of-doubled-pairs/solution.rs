pub fn can_reorder_doubled(arr: &[i64]) -> bool {
    let n = arr.len();
    let mut zeros: usize = 0;
    let mut pos: Vec<i64> = Vec::new();
    let mut neg: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let x = arr[i];
        if x == 0 {
            zeros += 1;
        } else if x > 0 {
            pos.push(x);
        } else {
            neg.push(-x);
        }
        i += 1;
    }

    if zeros % 2 != 0 {
        return false;
    }

    let pos_sorted = sorted_asc(&pos);
    let neg_sorted = sorted_asc(&neg);

    let ok_pos = check_group(&pos_sorted);
    if !ok_pos {
        return false;
    }
    check_group(&neg_sorted)
}

// Returns a new ascending-sorted copy of `v` using an iterative merge sort.
fn sorted_asc(v: &[i64]) -> Vec<i64> {
    let n = v.len();
    let mut w: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        w.push(v[i]);
        i += 1;
    }
    if n < 2 {
        return w;
    }

    let mut width: usize = 1;
    while width < n {
        let mut w2: Vec<i64> = Vec::new();
        let mut lo: usize = 0;
        while lo < n {
            let mid = if lo + width < n { lo + width } else { n };
            let hi = if lo + 2 * width < n { lo + 2 * width } else { n };

            let mut p = lo;
            let mut q = mid;
            while p < mid && q < hi {
                if w[p] <= w[q] {
                    w2.push(w[p]);
                    p += 1;
                } else {
                    w2.push(w[q]);
                    q += 1;
                }
            }
            while p < mid {
                w2.push(w[p]);
                p += 1;
            }
            while q < hi {
                w2.push(w[q]);
                q += 1;
            }
            lo += 2 * width;
        }

        let mut t = 0;
        while t < n {
            w[t] = w2[t];
            t += 1;
        }
        width *= 2;
    }
    w
}

// `v` is sorted ascending and all entries are positive.
// Greedily pair each unused element x with an unused element equal to 2*x.
// No early `return` statements inside loops (required by Aeneas translation).
fn check_group(v: &[i64]) -> bool {
    let n = v.len();
    if n % 2 != 0 {
        return false;
    }
    if n == 0 {
        return true;
    }

    let mut used: Vec<bool> = Vec::new();
    let mut t = 0;
    while t < n {
        used.push(false);
        t += 1;
    }

    let mut ok: bool = true;
    let mut j: usize = 0;
    let mut i: usize = 0;
    while i < n && ok {
        if used[i] {
            i += 1;
        } else {
            used[i] = true;
            let target = v[i] * 2;

            while j < n && (used[j] || v[j] < target) {
                j += 1;
            }

            if j >= n {
                ok = false;
            } else {
                if v[j] != target {
                    ok = false;
                } else {
                    used[j] = true;
                    i += 1;
                }
            }
        }
    }
    ok
}
