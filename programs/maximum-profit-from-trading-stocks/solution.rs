pub fn maximum_profit(present: &[i64], future: &[i64], budget: i64) -> i64 {
    let n = present.len();
    let b = budget as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= b {
        dp.push(0);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < n {
        let price = present[idx];
        let gain = future[idx] - present[idx];

        if gain > 0 && price <= budget {
            let mut c: i64 = budget;
            while c >= price {
                let ci = c as usize;
                let prev = (c - price) as usize;
                let candidate = dp[prev] + gain;
                if candidate > dp[ci] {
                    dp[ci] = candidate;
                }
                c -= 1;
            }
        }

        idx += 1;
    }

    dp[b]
}
