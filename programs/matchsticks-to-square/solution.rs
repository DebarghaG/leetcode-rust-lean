pub fn makesquare(matchsticks: &[i64]) -> bool {
    let n = matchsticks.len();
    if n == 0 {
        return false;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += matchsticks[i];
        i += 1;
    }

    if total % 4 != 0 {
        return false;
    }

    let target: i64 = total / 4;
    if target <= 0 {
        return false;
    }

    i = 0;
    while i < n {
        if matchsticks[i] > target {
            return false;
        }
        i += 1;
    }

    let mut size: usize = 1;
    i = 0;
    while i < n {
        size *= 2;
        i += 1;
    }

    let mut sums: Vec<i64> = Vec::new();
    let mut mask: usize = 0;
    while mask < size {
        let mut s: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            let bit: usize = 1 << j;
            if (mask & bit) != 0 {
                s += matchsticks[j];
            }
            j += 1;
        }
        sums.push(s);
        mask += 1;
    }

    let mut dp: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < size {
        dp.push(false);
        k += 1;
    }
    dp[0] = true;

    mask = 0;
    while mask < size {
        if dp[mask] {
            let rem: i64 = sums[mask] % target;
            let mut j: usize = 0;
            while j < n {
                let bit: usize = 1 << j;
                if (mask & bit) == 0 {
                    let val: i64 = matchsticks[j];
                    if rem + val <= target {
                        dp[mask | bit] = true;
                    }
                }
                j += 1;
            }
        }
        mask += 1;
    }

    dp[size - 1]
}
