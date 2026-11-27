pub fn winner_square_game(n: i64) -> bool {
    if n <= 0 {
        return false;
    }

    let nn: usize = n as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx <= nn {
        dp.push(0);
        idx += 1;
    }

    let mut i: usize = 1;
    while i <= nn {
        let mut win: bool = false;
        let mut k: usize = 1;

        while k * k <= i {
            if dp[i - k * k] == 0 {
                win = true;
            }
            k += 1;
        }

        if win {
            dp[i] = 1;
        } else {
            dp[i] = 0;
        }

        i += 1;
    }

    dp[nn] != 0
}
