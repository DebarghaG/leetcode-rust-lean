pub fn count_good_strings(low: i64, high: i64, zero: i64, one: i64) -> i64 {
    let modulo: i64 = 1000000007;

    let high_usize = high as usize;
    let low_usize = low as usize;
    let zero_usize = zero as usize;
    let one_usize = one as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= high_usize {
        dp.push(0);
        i += 1;
    }

    dp[0] = 1;

    let mut len: usize = 1;
    while len <= high_usize {
        let mut val: i64 = 0;

        if len >= zero_usize {
            val = val + dp[len - zero_usize];
            if val >= modulo {
                val = val - modulo;
            }
        }

        if len >= one_usize {
            val = val + dp[len - one_usize];
            if val >= modulo {
                val = val - modulo;
            }
        }

        dp[len] = val;
        len += 1;
    }

    let mut answer: i64 = 0;
    let mut j: usize = low_usize;
    while j <= high_usize {
        answer = answer + dp[j];
        if answer >= modulo {
            answer = answer - modulo;
        }
        j += 1;
    }

    answer
}
