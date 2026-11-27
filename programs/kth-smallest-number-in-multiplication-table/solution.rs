pub fn find_kth_number(m: i64, n: i64, k: i64) -> i64 {
    let total: i64 = m * n;
    let mut lo: i64 = 1;
    let mut hi: i64 = total;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        let count: i64 = count_leq(m, n, mid);

        if count >= k {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

fn count_leq(m: i64, n: i64, x: i64) -> i64 {
    let mut a: i64 = m;
    let mut b: i64 = n;

    if a > b {
        let t: i64 = a;
        a = b;
        b = t;
    }

    let mut count: i64 = 0;
    let mut i: i64 = 1;

    while i <= a {
        let q: i64 = x / i;
        if q >= b {
            count += b;
        } else {
            count += q;
        }
        i += 1;
    }

    count
}
