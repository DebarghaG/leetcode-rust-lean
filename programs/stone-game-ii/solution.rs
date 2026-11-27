pub fn stone_game_ii(piles: &[i64]) -> i64 {
    let n = piles.len();

    // suffix[i] = sum of piles[i..n]
    let mut suffix: Vec<i64> = Vec::new();
    let mut i = 0;
    while i <= n {
        suffix.push(0);
        i += 1;
    }

    let mut i = n;
    while i > 0 {
        i -= 1;
        suffix[i] = suffix[i + 1] + piles[i];
    }

    // dp[i][m] = maximum stones the current player can obtain
    // starting from pile i with current M = m.
    let cols = n + 2;
    let mut dp: Vec<Vec<i64>> = Vec::new();

    let mut r = 0;
    while r <= n {
        let mut row: Vec<i64> = Vec::new();
        let mut c = 0;
        while c < cols {
            row.push(0);
            c += 1;
        }
        dp.push(row);
        r += 1;
    }

    let mut ii = n;
    while ii > 0 {
        ii -= 1;

        let mut m = n;
        while m > 0 {
            let rem = n - ii;
            let mut limit = 2 * m;
            if limit > rem {
                limit = rem;
            }

            let mut best: i64 = 0;
            let mut x = 1;
            while x <= limit {
                let next_m = if m > x { m } else { x };
                let value = suffix[ii] - dp[ii + x][next_m];
                if value > best {
                    best = value;
                }
                x += 1;
            }

            dp[ii][m] = best;
            m -= 1;
        }
    }

    dp[0][1]
}
