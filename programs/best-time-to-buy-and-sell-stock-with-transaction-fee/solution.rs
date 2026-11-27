pub fn max_profit(prices: &[i64], fee: i64) -> i64 {
    let n = prices.len();
    if n == 0 {
        return 0;
    }

    let mut cash: i64 = 0;
    let mut hold: i64 = -prices[0];

    let mut i: usize = 1;
    while i < n {
        let price = prices[i];
        let old_cash = cash;

        let sell_value = hold + price - fee;
        if sell_value > cash {
            cash = sell_value;
        }

        let buy_value = old_cash - price;
        if buy_value > hold {
            hold = buy_value;
        }

        i += 1;
    }

    cash
}
