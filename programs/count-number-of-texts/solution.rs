pub fn count_texts(pressed_keys: &[u8]) -> i64 {
    let n = pressed_keys.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        dp.push(0);
        i += 1;
    }
    dp[0] = 1;

    i = 0;
    while i < n {
        let digit = pressed_keys[i];
        let max_presses: usize = if digit == b'7' || digit == b'9' { 4 } else { 3 };

        let mut k: usize = 1;
        let mut keep_going: bool = true;

        while k <= max_presses && k <= i + 1 && keep_going {
            let pos: usize = i + 1 - k;

            if pressed_keys[pos] == digit {
                let old_value = dp[i + 1];
                let add_value = dp[pos];
                dp[i + 1] = (old_value + add_value) % 1000000007;
                k += 1;
            } else {
                keep_going = false;
            }
        }

        i += 1;
    }

    dp[n]
}
