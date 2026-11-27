pub fn max_profit(prices: &[i64]) -> i64 {
    let n = prices.len();
    if n == 0 {
        return 0;
    }

    let neg_inf: i64 = -1000000000;
    let mut hold: i64 = neg_inf;
    let mut sold: i64 = neg_inf;
    let mut rest: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let p = prices[i];

        let prev_hold = hold;
        let prev_sold = sold;
        let prev_rest = rest;

        let buy = prev_rest - p;
        if prev_hold > buy {
            hold = prev_hold;
        } else {
            hold = buy;
        }

        sold = prev_hold + p;

        if prev_rest > prev_sold {
            rest = prev_rest;
        } else {
            rest = prev_sold;
        }

        i += 1;
    }

    if sold > rest {
        sold
    } else {
        rest
    }
}
