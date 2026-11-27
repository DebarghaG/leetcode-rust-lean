pub fn buy_choco(prices: &[i64], money: i64) -> i64 {
    let mut min1: i64 = 101;
    let mut min2: i64 = 101;

    let n = prices.len();
    let mut i: usize = 0;
    while i < n {
        let p = prices[i];
        if p < min1 {
            min2 = min1;
            min1 = p;
        } else if p < min2 {
            min2 = p;
        }
        i += 1;
    }

    let total = min1 + min2;
    if total <= money {
        money - total
    } else {
        money
    }
}
