pub fn super_egg_drop(k: i64, n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }
    if k <= 0 {
        return 0;
    }

    let kk = k as usize;
    let target = n;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i <= kk {
        dp.push(0);
        i += 1;
    }

    let mut moves: i64 = 0;
    while dp[kk] < target {
        moves += 1;

        let mut e = kk;
        while e > 0 {
            let mut val = dp[e] + dp[e - 1] + 1;
            if val > target {
                val = target;
            }
            dp[e] = val;
            e -= 1;
        }
    }

    moves
}
