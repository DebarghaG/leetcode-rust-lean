pub fn max_profit(prices: &[i64]) -> i64 {
    let n = prices.len();
    if n == 0 {
        return 0;
    }
    let mut min_price: i64 = prices[0];
    let mut best: i64 = 0;
    let mut i: usize = 1;
    while i < n {
        let p = prices[i];
        if p < min_price {
            min_price = p;
        } else {
            let profit = p - min_price;
            if profit > best {
                best = profit;
            }
        }
        i += 1;
    }
    best
}
