pub fn number_of_ways(numPeople: i64) -> i64 {
    let n: usize = (numPeople / 2) as usize;
    let modv: i64 = 1000000007;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx <= n {
        dp.push(0);
        idx += 1;
    }

    dp[0] = 1;

    let mut k: usize = 0;
    while k < n {
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i <= k {
            let term: i64 = (dp[i] * dp[k - i]) % modv;
            sum = (sum + term) % modv;
            i += 1;
        }
        dp[k + 1] = sum;
        k += 1;
    }

    dp[n]
}
