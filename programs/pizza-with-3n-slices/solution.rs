pub fn max_size_slices(slices: &[i64]) -> i64 {
    let m = slices.len();
    let k = m / 3;

    if k == 0 {
        return 0;
    }

    let without_last = max_non_adjacent(slices, 0, m - 1, k);
    let without_first = max_non_adjacent(slices, 1, m, k);

    if without_last > without_first {
        without_last
    } else {
        without_first
    }
}

fn max_non_adjacent(slices: &[i64], start: usize, end: usize, k: usize) -> i64 {
    let len = end - start;

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i <= len {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j <= k {
            row.push(-1);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    dp[0][0] = 0;

    i = 1;
    while i <= len {
        dp[i][0] = 0;
        let value = slices[start + i - 1];

        let mut j = 1;
        while j <= k {
            let mut best = dp[i - 1][j];

            let previous = if i >= 2 {
                dp[i - 2][j - 1]
            } else if j == 1 {
                0
            } else {
                -1
            };

            if previous >= 0 {
                let candidate = previous + value;
                if candidate > best {
                    best = candidate;
                }
            }

            dp[i][j] = best;
            j += 1;
        }

        i += 1;
    }

    dp[len][k]
}
