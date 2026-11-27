fn sort_i64(v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n <= 1 {
        return v;
    }
    let mut a = v;
    let mut tmp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if left + 2 * width < n { left + 2 * width } else { n };

            let mut p = left;
            let mut q = mid;
            let mut kk = left;

            while p < mid && q < right {
                if a[p] <= a[q] {
                    tmp[kk] = a[p];
                    p += 1;
                } else {
                    tmp[kk] = a[q];
                    q += 1;
                }
                kk += 1;
            }
            while p < mid {
                tmp[kk] = a[p];
                p += 1;
                kk += 1;
            }
            while q < right {
                tmp[kk] = a[q];
                q += 1;
                kk += 1;
            }

            left += 2 * width;
        }

        let mut idx: usize = 0;
        while idx < n {
            a[idx] = tmp[idx];
            idx += 1;
        }

        width *= 2;
    }

    a
}

fn feasible(p: &[i64], side: i64, d: i64, k: i64) -> bool {
    let n = p.len();
    if (n as i64) < k {
        return false;
    }
    let circum = 4 * side;

    // Necessary condition: k points each need arc >= d, total = circum.
    if d > 0 {
        if k > circum / d {
            return false;
        }
    }

    // Doubled positions so that circular search becomes linear search.
    let mut ext: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 2 * n {
        if i < n {
            ext.push(p[i]);
        } else {
            ext.push(p[i - n] + circum);
        }
        i += 1;
    }

    let mut found = false;
    let mut s: usize = 0;
    while s < n && !found {
        let start_pos = ext[s];
        let cap = start_pos + circum - d;
        let mut cur = s;
        let mut cnt: i64 = 1;
        let mut going = true;

        while going && !found {
            let target = ext[cur] + d;

            // lower_bound: smallest j >= cur+1 (within [s, s+n)) with ext[j] >= target
            let mut a = cur + 1;
            let mut b = s + n;
            while a < b {
                let m = (a + b) / 2;
                if ext[m] < target {
                    a = m + 1;
                } else {
                    b = m;
                }
            }

            if a < s + n && ext[a] <= cap {
                cur = a;
                cnt += 1;
                if cnt >= k {
                    found = true;
                }
            } else {
                going = false;
            }
        }

        s += 1;
    }

    found
}

pub fn max_distance(side: i64, points: &[Vec<i64>], k: i64) -> i64 {
    let mut pvals: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < points.len() {
        let x = points[i][0];
        let y = points[i][1];

        // Map boundary point to a unique perimeter position in [0, 4*side).
        let mut p: i64 = -1;
        if y == 0 {
            p = x; // bottom edge
        } else if x == side {
            p = side + y; // right edge
        } else if y == side {
            p = 2 * side + (side - x); // top edge
        } else if x == 0 {
            p = 3 * side + (side - y); // left edge
        }

        if p >= 0 {
            pvals.push(p);
        }
        i += 1;
    }

    let sorted = sort_i64(pvals);

    let mut lo: i64 = 0;
    let mut hi: i64 = side;
    while lo < hi {
        let mid = (lo + hi + 1) / 2;
        if feasible(&sorted, side, mid, k) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}
