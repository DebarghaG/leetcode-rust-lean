fn sorted_copy(xs: &[i64]) -> Vec<i64> {
    let n = xs.len();
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(xs[i]);
        i += 1;
    }

    if n < 2 {
        return v;
    }

    let mut tmp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = start + 2 * width;
            if end > n {
                end = n;
            }

            if mid < end {
                let mut a = start;
                let mut b = mid;
                let mut k = start;

                while a < mid && b < end {
                    if v[a] <= v[b] {
                        tmp[k] = v[a];
                        a += 1;
                    } else {
                        tmp[k] = v[b];
                        b += 1;
                    }
                    k += 1;
                }

                while a < mid {
                    tmp[k] = v[a];
                    a += 1;
                    k += 1;
                }

                while b < end {
                    tmp[k] = v[b];
                    b += 1;
                    k += 1;
                }

                let mut p = start;
                while p < end {
                    v[p] = tmp[p];
                    p += 1;
                }
            }

            start += 2 * width;
        }

        width = width * 2;
    }

    v
}

pub fn find_radius(houses: &[i64], heaters: &[i64]) -> i64 {
    let hs = sorted_copy(houses);
    let ht = sorted_copy(heaters);

    let n = hs.len();
    let m = ht.len();

    if n == 0 || m == 0 {
        return 0;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let h = hs[i];

        let mut lo: usize = 0;
        let mut hi: usize = m;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if ht[mid] < h {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        let mut d: i64 = 0;

        if lo == 0 {
            d = ht[0] - h;
        } else if lo == m {
            d = h - ht[m - 1];
        } else {
            let left = h - ht[lo - 1];
            let right = ht[lo] - h;
            if left < right {
                d = left;
            } else {
                d = right;
            }
        }

        if d > ans {
            ans = d;
        }

        i += 1;
    }

    ans
}
