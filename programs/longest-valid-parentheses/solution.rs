pub fn longest_valid_parentheses(s: &[u8]) -> i64 {
    let n = s.len();
    let mut dp: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        dp.push(0);
        i += 1;
    }

    let mut best: i64 = 0;
    let mut i = 0;

    while i < n {
        if s[i] == b')' {
            if i >= 1 && s[i - 1] == b'(' {
                if i >= 2 {
                    dp[i] = dp[i - 2] + 2;
                } else {
                    dp[i] = 2;
                }
            } else if i >= 1 && s[i - 1] == b')' {
                let prev = dp[i - 1];

                if prev + 1 <= i as i64 {
                    let j: usize = i - (prev as usize) - 1;

                    if s[j] == b'(' {
                        dp[i] = prev + 2;

                        if j >= 1 {
                            dp[i] = dp[i] + dp[j - 1];
                        }
                    }
                }
            }

            if dp[i] > best {
                best = dp[i];
            }
        }

        i += 1;
    }

    best
}
