pub fn max_tastiness(price: &[i64], tastiness: &[i64], maxAmount: i64, maxCoupons: i64) -> i64 {
    if maxAmount < 0 || maxCoupons < 0 {
        return 0;
    }

    let amount_limit = maxAmount as usize;
    let coupon_limit = maxCoupons as usize;
    let cols = amount_limit + 1;

    let mut n = price.len();
    if tastiness.len() < n {
        n = tastiness.len();
    }

    if n == 0 {
        return 0;
    }

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut c = 0usize;
    while c <= coupon_limit {
        let mut row: Vec<i64> = Vec::new();
        row.push(0);
        let mut a = 1usize;
        while a < cols {
            row.push(-1);
            a += 1;
        }
        dp.push(row);
        c += 1;
    }

    let mut i = 0usize;
    while i < n {
        let mut p_i64 = price[i];
        if p_i64 < 0 {
            p_i64 = 0;
        }
        let t = tastiness[i];
        let p = p_i64 as usize;
        let half = (p_i64 / 2) as usize;

        let mut curr: Vec<Vec<i64>> = Vec::new();
        c = 0;
        while c <= coupon_limit {
            let mut row: Vec<i64> = Vec::new();
            let mut a = 0usize;
            while a < cols {
                row.push(-1);
                a += 1;
            }
            curr.push(row);
            c += 1;
        }

        c = 0;
        while c <= coupon_limit {
            let mut a = 0usize;
            while a < cols {
                let val = dp[c][a];
                if val >= 0 {
                    if val > curr[c][a] {
                        curr[c][a] = val;
                    }

                    if a + p <= amount_limit {
                        let cand = val + t;
                        if cand > curr[c][a + p] {
                            curr[c][a + p] = cand;
                        }
                    }

                    if c < coupon_limit && a + half <= amount_limit {
                        let cand = val + t;
                        if cand > curr[c + 1][a + half] {
                            curr[c + 1][a + half] = cand;
                        }
                    }
                }
                a += 1;
            }
            c += 1;
        }

        dp = curr;
        i += 1;
    }

    let mut ans: i64 = 0;
    c = 0;
    while c <= coupon_limit {
        let mut a = 0usize;
        while a < cols {
            if dp[c][a] > ans {
                ans = dp[c][a];
            }
            a += 1;
        }
        c += 1;
    }

    ans
}
