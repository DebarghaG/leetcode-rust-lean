pub fn num_tilings(n: i64) -> i64 {
    let md: i64 = 1000000007;

    if n == 0 {
        return 1;
    }
    if n == 1 {
        return 1;
    }
    if n == 2 {
        return 2;
    }

    let n_usize: usize = n as usize;

    // History vector: dp[k] = number of tilings of a 2 x k board.
    let mut dp: Vec<i64> = Vec::new();
    dp.push(1); // f(0)
    dp.push(1); // f(1)
    dp.push(2); // f(2)

    let mut ans: i64 = 2;
    let mut i: usize = 3;
    while i <= n_usize {
        let a: i64 = dp[i - 1];
        let b: i64 = dp[i - 3];
        let val: i64 = (2 * a + b) % md;
        dp.push(val);
        ans = val;
        i += 1;
    }

    ans
}
