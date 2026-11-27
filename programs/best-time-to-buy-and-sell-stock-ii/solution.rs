pub fn max_profit(prices: &[i64]) -> i64 {
    let mut profit: i64 = 0;
    let n = prices.len();
    let mut i: usize = 1;

    while i < n {
        let diff = prices[i] - prices[i - 1];
        if diff > 0 {
            profit += diff;
        }
        i += 1;
    }

    profit
}
