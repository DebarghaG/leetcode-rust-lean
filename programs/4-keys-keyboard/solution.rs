pub fn max_a(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let m = n as usize;
    let mut dp: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k <= m {
        dp.push(0);
        k += 1;
    }

    let mut i: usize = 1;
    while i <= m {
        // Option 1: press 'A' once.
        let mut best: i64 = dp[i - 1] + 1;

        // Option 2: after j presses, use Ctrl-A, Ctrl-C,
        // then the remaining presses as Ctrl-V.
        let mut j: usize = 1;
        while j + 3 <= i {
            let candidate = dp[j] * ((i - j - 1) as i64);
            if candidate > best {
                best = candidate;
            }
            j += 1;
        }

        dp[i] = best;
        i += 1;
    }

    dp[m]
}
