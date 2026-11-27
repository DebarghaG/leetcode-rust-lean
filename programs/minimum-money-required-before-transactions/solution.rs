pub fn minimum_money(transactions: &[Vec<i64>]) -> i64 {
    let n: usize = transactions.len();
    let mut total_loss: i64 = 0;
    let mut max_min: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let cost: i64 = transactions[i][0];
        let cashback: i64 = transactions[i][1];

        let diff: i64 = cost - cashback;
        if diff > 0 {
            total_loss += diff;
        }

        let m: i64 = if cost < cashback { cost } else { cashback };
        if m > max_min {
            max_min = m;
        }

        i += 1;
    }

    total_loss + max_min
}
