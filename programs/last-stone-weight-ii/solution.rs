pub fn last_stone_weight_ii(stones: &[i64]) -> i64 {
    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < stones.len() {
        total = total + stones[i];
        i = i + 1;
    }

    let target: i64 = total / 2;
    let target_usize: usize = target as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= target_usize {
        dp.push(0);
        j = j + 1;
    }
    dp[0] = 1;

    let mut k: usize = 0;
    while k < stones.len() {
        let w: i64 = stones[k];
        if w <= target {
            let mut s: i64 = target;
            while s >= w {
                let idx: usize = s as usize;
                let prev: usize = (s - w) as usize;
                if dp[prev] == 1 {
                    dp[idx] = 1;
                }
                s = s - 1;
            }
        }
        k = k + 1;
    }

    let mut best: i64 = 0;
    let mut s: i64 = target;
    while s >= 0 {
        let idx: usize = s as usize;
        if dp[idx] == 1 {
            best = s;
            break;
        }
        s = s - 1;
    }

    total - 2 * best
}
