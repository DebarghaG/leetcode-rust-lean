pub fn get_money_amount(n: i64) -> i64 {
    let n_usize = n as usize;
    let size = n_usize + 2;

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut i0: usize = 0;
    while i0 < size {
        let mut row: Vec<i64> = Vec::new();
        let mut j0: usize = 0;
        while j0 < size {
            row.push(0);
            j0 += 1;
        }
        dp.push(row);
        i0 += 1;
    }

    let mut len: usize = 2;
    while len <= n_usize {
        let mut left: usize = 1;
        while left + len - 1 <= n_usize {
            let right = left + len - 1;
            let mut best: i64 = 1000000000;

            let mut guess: usize = left;
            while guess <= right {
                let a = dp[left][guess - 1];
                let b = dp[guess + 1][right];
                let mut worst = a;
                if b > worst {
                    worst = b;
                }

                let candidate = guess as i64 + worst;
                if candidate < best {
                    best = candidate;
                }

                guess += 1;
            }

            dp[left][right] = best;
            left += 1;
        }
        len += 1;
    }

    dp[1][n_usize]
}
