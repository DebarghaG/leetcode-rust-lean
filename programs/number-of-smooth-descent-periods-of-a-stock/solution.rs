pub fn get_descent_periods(prices: &[i64]) -> i64 {
    let n = prices.len();
    if n == 0 {
        return 0;
    }
    let mut total: i64 = 1;
    let mut run: i64 = 1;
    let mut i: usize = 1;
    while i < n {
        if prices[i - 1] - prices[i] == 1 {
            run += 1;
        } else {
            run = 1;
        }
        total += run;
        i += 1;
    }
    total
}
