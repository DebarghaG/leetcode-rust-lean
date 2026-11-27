fn letter_distance(a: usize, b: usize) -> i64 {
    let r1 = (a / 6) as i64;
    let c1 = (a % 6) as i64;
    let r2 = (b / 6) as i64;
    let c2 = (b % 6) as i64;

    let mut dr = r1 - r2;
    if dr < 0 {
        dr = -dr;
    }

    let mut dc = c1 - c2;
    if dc < 0 {
        dc = -dc;
    }

    dr + dc
}

pub fn minimum_distance(word: &[u8]) -> i64 {
    let n = word.len();
    if n == 0 {
        return 0;
    }

    // dp[j] = minimum cost after typing the processed prefix, where one finger
    // is on the last typed letter and the other finger is on letter j.
    let mut dp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < 26 {
        dp.push(0);
        j += 1;
    }

    let mut i: usize = 1;
    while i < n {
        let prev = (word[i - 1] - b'A') as usize;
        let cur = (word[i] - b'A') as usize;

        let mut ndp: Vec<i64> = Vec::new();
        j = 0;
        while j < 26 {
            ndp.push(1000000000);
            j += 1;
        }

        let d_prev_cur = letter_distance(prev, cur);

        j = 0;
        while j < 26 {
            // Move the finger currently on prev to cur.
            let move_current = dp[j] + d_prev_cur;
            if move_current < ndp[j] {
                ndp[j] = move_current;
            }

            // Move the other finger from j to cur; the previous finger stays on prev.
            let move_other = dp[j] + letter_distance(j, cur);
            if move_other < ndp[prev] {
                ndp[prev] = move_other;
            }

            j += 1;
        }

        dp = ndp;
        i += 1;
    }

    let mut ans = dp[0];
    j = 1;
    while j < 26 {
        if dp[j] < ans {
            ans = dp[j];
        }
        j += 1;
    }

    ans
}
