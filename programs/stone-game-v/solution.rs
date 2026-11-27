pub fn stone_game_v(stoneValue: &[i64]) -> i64 {
    let n = stoneValue.len();
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 0;
    }

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);
    let mut i: usize = 0;
    while i < n {
        let next = prefix[i] + stoneValue[i];
        prefix.push(next);
        i += 1;
    }

    let mut dp: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            row.push(0);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    let mut len: usize = 2;
    while len <= n {
        let mut left_index: usize = 0;
        while left_index + len <= n {
            let right_index = left_index + len - 1;

            let mut best: i64 = 0;
            let mut split: usize = left_index;

            while split < right_index {
                let left_sum = prefix[split + 1] - prefix[left_index];
                let right_sum = prefix[right_index + 1] - prefix[split + 1];

                let mut candidate: i64 = 0;

                if left_sum < right_sum {
                    candidate = dp[left_index][split] + left_sum;
                } else if left_sum > right_sum {
                    candidate = dp[split + 1][right_index] + right_sum;
                } else {
                    let a = dp[left_index][split];
                    let b = dp[split + 1][right_index];
                    let better = if a > b { a } else { b };
                    candidate = better + left_sum;
                }

                if candidate > best {
                    best = candidate;
                }

                split += 1;
            }

            dp[left_index][right_index] = best;
            left_index += 1;
        }
        len += 1;
    }

    dp[0][n - 1]
}
