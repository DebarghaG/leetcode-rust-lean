fn sort_i64(mut a: Vec<i64>) -> Vec<i64> {
    let n = a.len();
    if n <= 1 {
        return a;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut width = 1usize;
    while width < n {
        let mut lo = 0usize;
        while lo < n {
            let mid = if lo + width < n { lo + width } else { n };
            let hi = if lo + width * 2 < n { lo + width * 2 } else { n };

            let mut p = lo;
            let mut q = mid;
            let mut k = lo;

            while p < mid && q < hi {
                if a[p] <= a[q] {
                    tmp[k] = a[p];
                    p += 1;
                } else {
                    tmp[k] = a[q];
                    q += 1;
                }
                k += 1;
            }

            while p < mid {
                tmp[k] = a[p];
                p += 1;
                k += 1;
            }

            while q < hi {
                tmp[k] = a[q];
                q += 1;
                k += 1;
            }

            lo = hi;
        }

        let mut c = 0usize;
        while c < n {
            a[c] = tmp[c];
            c += 1;
        }

        width = width * 2;
    }

    a
}

fn lower_bound(v: &[i64], x: i64) -> usize {
    let mut lo = 0usize;
    let mut hi = v.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

pub fn valid_arrangement(pairs: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = pairs.len();
    if n == 0 {
        return Vec::new();
    }

    let mut values: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        values.push(pairs[i][0]);
        values.push(pairs[i][1]);
        i += 1;
    }

    values = sort_i64(values);

    let mut uniq: Vec<i64> = Vec::new();
    let mut j = 0usize;
    while j < values.len() {
        if j == 0 {
            uniq.push(values[j]);
        } else if values[j] != values[j - 1] {
            uniq.push(values[j]);
        }
        j += 1;
    }

    let m = uniq.len();

    let mut head: Vec<i64> = Vec::new();
    let mut out_deg: Vec<i64> = Vec::new();
    let mut in_deg: Vec<i64> = Vec::new();

    let mut v = 0usize;
    while v < m {
        head.push(-1);
        out_deg.push(0);
        in_deg.push(0);
        v += 1;
    }

    let mut dest: Vec<i64> = Vec::new();
    let mut edge_next: Vec<i64> = Vec::new();

    let mut e = 0usize;
    while e < n {
        let u = lower_bound(&uniq, pairs[e][0]) as i64;
        let w = lower_bound(&uniq, pairs[e][1]) as i64;

        dest.push(w);
        edge_next.push(head[u as usize]);
        head[u as usize] = e as i64;

        out_deg[u as usize] += 1;
        in_deg[w as usize] += 1;

        e += 1;
    }

    let mut start: i64 = -1;
    let mut q = 0usize;
    while q < m {
        if out_deg[q] > in_deg[q] {
            start = q as i64;
            break;
        }
        q += 1;
    }

    if start == -1 {
        start = lower_bound(&uniq, pairs[0][0]) as i64;
    }

    let mut stack_v: Vec<i64> = Vec::new();
    let mut sp_v = 0usize;
    stack_v.push(start);
    sp_v += 1;

    let mut stack_e: Vec<i64> = Vec::new();
    let mut sp_e = 0usize;

    let mut path_rev: Vec<i64> = Vec::new();

    while sp_v > 0 {
        let u = stack_v[sp_v - 1];
        let ui = u as usize;
        let next_e = head[ui];

        if next_e != -1 {
            let edge = next_e;
            head[ui] = edge_next[edge as usize];
            let w = dest[edge as usize];

            if sp_e == stack_e.len() {
                stack_e.push(edge);
            } else {
                stack_e[sp_e] = edge;
            }
            sp_e += 1;

            if sp_v == stack_v.len() {
                stack_v.push(w);
            } else {
                stack_v[sp_v] = w;
            }
            sp_v += 1;
        } else {
            sp_v -= 1;

            if sp_e > 0 {
                let edge = stack_e[sp_e - 1];
                sp_e -= 1;
                path_rev.push(edge);
            }
        }
    }

    let mut result: Vec<Vec<i64>> = Vec::new();
    let mut t = path_rev.len();

    while t > 0 {
        t -= 1;
        let edge = path_rev[t] as usize;

        let mut row: Vec<i64> = Vec::new();
        row.push(pairs[edge][0]);
        row.push(pairs[edge][1]);
        result.push(row);
    }

    result
}
