const MOD: i64 = 1_000_000_007;

fn sorted_cuts(cuts: &[i64]) -> Vec<i64> {
    let n = cuts.len();
    let mut v: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        v.push(cuts[t]);
        t += 1;
    }

    if n < 2 {
        return v;
    }

    let mut aux: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        aux.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut i: usize = 0;
        while i < n {
            let mut mid = i + width;
            if mid > n {
                mid = n;
            }

            let mut end = i + width * 2;
            if end > n {
                end = n;
            }

            let mut p = i;
            let mut q = mid;
            let mut k = i;

            while p < mid && q < end {
                if v[p] <= v[q] {
                    aux[k] = v[p];
                    p += 1;
                } else {
                    aux[k] = v[q];
                    q += 1;
                }
                k += 1;
            }

            while p < mid {
                aux[k] = v[p];
                p += 1;
                k += 1;
            }

            while q < end {
                aux[k] = v[q];
                q += 1;
                k += 1;
            }

            i += width * 2;
        }

        let mut j: usize = 0;
        while j < n {
            v[j] = aux[j];
            j += 1;
        }

        width = width * 2;
    }

    v
}

fn max_gap(limit: i64, cuts: &[i64]) -> i64 {
    let v = sorted_cuts(cuts);
    let n = v.len();

    let mut best: i64 = 0;
    let mut prev: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let gap = v[i] - prev;
        if gap > best {
            best = gap;
        }
        prev = v[i];
        i += 1;
    }

    let last_gap = limit - prev;
    if last_gap > best {
        best = last_gap;
    }

    best
}

pub fn max_area(h: i64, w: i64, horizontalCuts: &[i64], verticalCuts: &[i64]) -> i64 {
    let max_horizontal = max_gap(h, horizontalCuts);
    let max_vertical = max_gap(w, verticalCuts);

    ((max_horizontal % MOD) * (max_vertical % MOD)) % MOD
}
