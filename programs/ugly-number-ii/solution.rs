pub fn nth_ugly_number(n: i64) -> i64 {
    let mut dp: Vec<i64> = Vec::new();
    dp.push(1);

    let mut i2: usize = 0;
    let mut i3: usize = 0;
    let mut i5: usize = 0;

    let mut count: i64 = 1;

    while count < n {
        let candidate2 = dp[i2] * 2;
        let candidate3 = dp[i3] * 3;
        let candidate5 = dp[i5] * 5;

        let mut next: i64 = candidate2;
        if candidate3 < next {
            next = candidate3;
        }
        if candidate5 < next {
            next = candidate5;
        }

        dp.push(next);

        while dp[i2] * 2 <= next {
            i2 += 1;
        }
        while dp[i3] * 3 <= next {
            i3 += 1;
        }
        while dp[i5] * 5 <= next {
            i5 += 1;
        }

        count += 1;
    }

    let last: usize = dp.len() - 1;
    dp[last]
}
