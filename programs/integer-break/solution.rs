pub fn integer_break(n: i64) -> i64 {
    let m = n as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i <= m {
        dp.push(0);
        i += 1;
    }

    dp[1] = 1;

    i = 2;
    while i <= m {
        let mut best = 0i64;
        let mut j = 1usize;
        while j < i {
            let left = j as i64;
            let right = (i - j) as i64;

            let mut value = left * right;
            if value > best {
                best = value;
            }

            value = left * dp[i - j];
            if value > best {
                best = value;
            }

            j += 1;
        }

        dp[i] = best;
        i += 1;
    }

    dp[m]
}
