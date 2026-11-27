pub fn calculate_minimum_hp(dungeon: &[Vec<i64>]) -> i64 {
    let m = dungeon.len();
    if m == 0 {
        return 1;
    }

    let n = dungeon[0].len();
    if n == 0 {
        return 1;
    }

    let inf: i64 = 1000000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        dp.push(inf);
        k += 1;
    }

    let mut i: usize = m;
    while i > 0 {
        i -= 1;

        let mut j: usize = n;
        while j > 0 {
            j -= 1;

            let val = dungeon[i][j];
            let mut need: i64 = 1;

            if i + 1 == m && j + 1 == n {
                need = 1 - val;
            } else {
                let mut best: i64 = inf;

                if i + 1 < m {
                    let down = dp[j];
                    if down < best {
                        best = down;
                    }
                }

                if j + 1 < n {
                    let right = dp[j + 1];
                    if right < best {
                        best = right;
                    }
                }

                need = best - val;
            }

            if need < 1 {
                need = 1;
            }

            dp[j] = need;
        }
    }

    dp[0]
}
