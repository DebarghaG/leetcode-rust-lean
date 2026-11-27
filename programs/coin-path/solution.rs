pub fn cheapest_jump(coins: &[i64], maxJump: i64) -> Vec<i64> {
    let n = coins.len();
    if n == 0 {
        return Vec::new();
    }

    let inf: i64 = 1000000000000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dp.push(inf);
        i += 1;
    }

    if coins[n - 1] != -1 {
        dp[n - 1] = coins[n - 1];
    }

    let mut i: usize = n - 1;
    while i > 0 {
        i -= 1;
        if coins[i] != -1 {
            let mut best: i64 = inf;
            let mut j: usize = i + 1;
            let mut d: i64 = 1;
            while j < n && d <= maxJump {
                if dp[j] < best {
                    best = dp[j];
                }
                j += 1;
                d += 1;
            }
            if best < inf / 2 {
                dp[i] = coins[i] + best;
            }
        }
    }

    if coins[0] == -1 || dp[0] >= inf / 2 {
        return Vec::new();
    }

    let mut ans: Vec<i64> = Vec::new();
    ans.push(1);

    let mut pos: usize = 0;
    while pos < n - 1 {
        let target: i64 = dp[pos] - coins[pos];

        let mut found: bool = false;
        let mut next: usize = pos + 1;
        let mut j: usize = pos + 1;
        let mut d: i64 = 1;

        while j < n && d <= maxJump && !found {
            if dp[j] == target {
                next = j;
                found = true;
            } else {
                j += 1;
                d += 1;
            }
        }

        if !found {
            return Vec::new();
        }

        ans.push((next + 1) as i64);
        pos = next;
    }

    ans
}
