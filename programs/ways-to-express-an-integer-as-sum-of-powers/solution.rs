pub fn number_of_ways(n: i64, x: i64) -> i64 {
    let nn = n as usize;
    let mut dp: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i <= nn {
        dp.push(0);
        i += 1;
    }
    dp[0] = 1;

    let md: i64 = 1000000007;
    let mut base: i64 = 1;

    while base <= n {
        let mut p: i64 = 1;
        let mut e: i64 = 0;

        while e < x {
            p = p * base;
            e += 1;
        }

        if p > n {
            break;
        }

        let mut s: i64 = n;
        while s >= p {
            let idx = s as usize;
            let prev = (s - p) as usize;
            dp[idx] = (dp[idx] + dp[prev]) % md;
            s -= 1;
        }

        base += 1;
    }

    dp[nn]
}
