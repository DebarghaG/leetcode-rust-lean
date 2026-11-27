pub fn max_profit(prices: &[i64]) -> i64 {
    let n = prices.len();
    if n == 0 {
        return 0;
    }

    let neg_inf: i64 = -1000000000000000000;
    let mut buy1 = neg_inf;
    let mut sell1 = 0;
    let mut buy2 = neg_inf;
    let mut sell2 = 0;

    let mut i = 0;
    while i < n {
        let p = prices[i];

        let candidate_buy1 = -p;
        if candidate_buy1 > buy1 {
            buy1 = candidate_buy1;
        }

        let candidate_sell1 = buy1 + p;
        if candidate_sell1 > sell1 {
            sell1 = candidate_sell1;
        }

        let candidate_buy2 = sell1 - p;
        if candidate_buy2 > buy2 {
            buy2 = candidate_buy2;
        }

        let candidate_sell2 = buy2 + p;
        if candidate_sell2 > sell2 {
            sell2 = candidate_sell2;
        }

        i += 1;
    }

    sell2
}
