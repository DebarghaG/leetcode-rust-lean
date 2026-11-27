pub fn stone_game(piles: &[i64]) -> bool {
    let n = piles.len();

    if n == 0 {
        return false;
    }

    // dp[i] stores the optimal score difference (current player - other player)
    // for the current interval length starting at i.
    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dp.push(piles[i]);
        i += 1;
    }

    let mut len: usize = 2;
    while len <= n {
        let count = n - len + 1;
        let mut start: usize = 0;

        while start < count {
            let end = start + len - 1;

            // Take the left pile:
            // current gets piles[start], then opponent is to move on [start+1, end],
            // whose optimal advantage is dp[start+1].
            let take_left = piles[start] - dp[start + 1];

            // Take the right pile:
            // current gets piles[end], then opponent is to move on [start, end-1],
            // whose optimal advantage is dp[start].
            let take_right = piles[end] - dp[start];

            if take_left > take_right {
                dp[start] = take_left;
            } else {
                dp[start] = take_right;
            }

            start += 1;
        }

        len += 1;
    }

    dp[0] > 0
}
