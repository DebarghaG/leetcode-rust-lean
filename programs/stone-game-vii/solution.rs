pub fn stone_game_vii(stones: &[i64]) -> i64 {
    let n = stones.len();
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
        let prev = prefix[i];
        prefix.push(prev + stones[i]);
        i += 1;
    }

    let total = n * n;
    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < total {
        dp.push(0);
        k += 1;
    }

    let mut len: usize = 2;
    while len <= n {
        let mut left: usize = 0;
        while left + len <= n {
            let right = left + len - 1;

            let remove_left_gain = prefix[right + 1] - prefix[left + 1];
            let remove_right_gain = prefix[right] - prefix[left];

            let take_left = remove_left_gain - dp[(left + 1) * n + right];
            let take_right = remove_right_gain - dp[left * n + (right - 1)];

            let best = if take_left > take_right {
                take_left
            } else {
                take_right
            };

            dp[left * n + right] = best;
            left += 1;
        }
        len += 1;
    }

    dp[n - 1]
}
