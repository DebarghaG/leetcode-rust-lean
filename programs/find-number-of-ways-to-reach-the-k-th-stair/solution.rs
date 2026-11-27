fn comb(n: i64, r: i64) -> i64 {
    if r < 0 || r > n {
        return 0;
    }

    let mut rr = r;
    if rr > n - r {
        rr = n - r;
    }

    let mut res: i64 = 1;
    let mut i: i64 = 1;
    while i <= rr {
        res = res * (n - rr + i) / i;
        i += 1;
    }
    res
}

pub fn ways_to_reach_stair(k: i64) -> i64 {
    let mut ans: i64 = 0;
    let mut i: i64 = 0;
    let mut pow: i64 = 1;

    while i <= 31 {
        let d: i64 = pow - k;

        if d >= 0 && d <= i + 1 {
            ans += comb(i + 1, d);
        }

        pow *= 2;
        i += 1;
    }

    ans
}
