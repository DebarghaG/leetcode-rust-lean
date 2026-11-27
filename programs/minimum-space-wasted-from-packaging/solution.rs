fn sort_vec(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n <= 1 {
        return v;
    }

    let mut width: usize = 1;
    while width < n {
        let mut temp: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < n {
            temp.push(0);
            z += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let mid = if i + width < n { i + width } else { n };
            let end = if mid + width < n { mid + width } else { n };

            let mut l = i;
            let mut r = mid;
            let mut k = i;

            while l < mid && r < end {
                if v[l] <= v[r] {
                    temp[k] = v[l];
                    l += 1;
                } else {
                    temp[k] = v[r];
                    r += 1;
                }
                k += 1;
            }

            while l < mid {
                temp[k] = v[l];
                l += 1;
                k += 1;
            }

            while r < end {
                temp[k] = v[r];
                r += 1;
                k += 1;
            }

            i = end;
        }

        let mut j: usize = 0;
        while j < n {
            v[j] = temp[j];
            j += 1;
        }

        width = width * 2;
    }

    v
}

fn upper_bound(xs: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] <= x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

pub fn min_wasted_space(packages: &[i64], boxes: &[Vec<i64>]) -> i64 {
    let n = packages.len();
    if n == 0 {
        return 0;
    }

    let mut p: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        p.push(packages[i]);
        i += 1;
    }
    p = sort_vec(p);

    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);
    let mut s: i64 = 0;
    let mut i2: usize = 0;
    while i2 < n {
        s += p[i2];
        pref.push(s);
        i2 += 1;
    }

    let m = boxes.len();
    let mut best: i64 = -1;
    let mut si: usize = 0;

    while si < m {
        let row = &boxes[si];

        let mut b: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < row.len() {
            b.push(row[j]);
            j += 1;
        }
        b = sort_vec(b);

        let blen = b.len();
        if blen > 0 {
            if b[blen - 1] >= p[n - 1] {
                let mut prev: usize = 0;
                let mut waste: i64 = 0;

                let mut k: usize = 0;
                while k < blen {
                    let x = b[k];
                    let cnt = upper_bound(&p, x);

                    if cnt > prev {
                        let c = (cnt - prev) as i64;
                        waste += c * x - (pref[cnt] - pref[prev]);
                        prev = cnt;
                    }

                    if prev == n {
                        break;
                    }

                    k += 1;
                }

                if prev == n {
                    if best < 0 || waste < best {
                        best = waste;
                    }
                }
            }
        }

        si += 1;
    }

    if best < 0 {
        -1
    } else {
        best % 1000000007
    }
}
