pub fn minimum_coins(prices: &[i64]) -> i64 {
    let n = prices.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n + 2 {
        dp.push(0);
        k += 1;
    }

    let mut dq: Vec<usize> = Vec::new();
    let mut k2: usize = 0;
    while k2 < n + 2 {
        dq.push(0);
        k2 += 1;
    }

    dp[1] = prices[0];
    dq[0] = 1;

    let mut head: usize = 0;
    let mut tail: usize = 1;
    let mut i: usize = 2;

    while i <= n + 1 {
        let left: usize = i / 2;

        while head < tail && dq[head] < left {
            head += 1;
        }

        let best: i64 = dp[dq[head]];

        let mut price: i64 = 0;
        if i <= n {
            price = prices[i - 1];
        }

        dp[i] = best + price;

        while tail > head && dp[dq[tail - 1]] >= dp[i] {
            tail -= 1;
        }

        dq[tail] = i;
        tail += 1;
        i += 1;
    }

    dp[n + 1]
}
