pub fn num_music_playlists(n: i64, goal: i64, k: i64) -> i64 {
    let modulo: i64 = 1000000007;
    let n_us = n as usize;
    let goal_us = goal as usize;

    let mut dp: Vec<Vec<i64>> = Vec::new();

    let mut i = 0usize;
    while i <= goal_us {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j <= n_us {
            row.push(0);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    dp[0][0] = 1;

    let mut len = 1usize;
    while len <= goal_us {
        let mut distinct = 1usize;
        while distinct <= n_us {
            let new_song_choices = n - (distinct as i64) + 1;
            let add_new = dp[len - 1][distinct - 1] * new_song_choices % modulo;

            let mut repeat_old = 0i64;
            if (distinct as i64) > k {
                let old_song_choices = (distinct as i64) - k;
                repeat_old = dp[len - 1][distinct] * old_song_choices % modulo;
            }

            let value = (add_new + repeat_old) % modulo;
            dp[len][distinct] = value;

            distinct += 1;
        }
        len += 1;
    }

    dp[goal_us][n_us]
}
