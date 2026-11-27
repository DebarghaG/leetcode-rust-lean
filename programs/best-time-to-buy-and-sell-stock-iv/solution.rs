pub fn max_profit(k: i64, prices: &[i64]) -> i64 {
    if k <= 0 {
        return 0;
    }

    let n = prices.len();
    if n < 2 {
        return 0;
    }

    let kk = k as usize;
    let mut buy: Vec<i64> = Vec::new();
    let mut sell: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i <= kk {
        buy.push(-1000000000);
        sell.push(0);
        i += 1;
    }

    let mut d = 0usize;
    while d < n {
        let price = prices[d];
        let mut j = kk;
        while j >= 1 {
            let candidate_buy = sell[j - 1] - price;
            if candidate_buy > buy[j] {
                buy[j] = candidate_buy;
            }

            let candidate_sell = buy[j] + price;
            if candidate_sell > sell[j] {
                sell[j] = candidate_sell;
            }

            j -= 1;
        }
        d += 1;
    }

    sell[kk]
}
