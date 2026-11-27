pub fn ways_to_reach_target(target: i64, types: &[Vec<i64>]) -> i64 {
    let modv: i64 = 1000000007;
    let target_usize: usize = target as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= target_usize {
        dp.push(0);
        i = i + 1;
    }
    dp[0] = 1;

    let n: usize = types.len();
    let mut ti: usize = 0;

    while ti < n {
        let count: usize = types[ti][0] as usize;
        let marks: usize = types[ti][1] as usize;

        let mut next: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= target_usize {
            next.push(0);
            j = j + 1;
        }

        let mut s: usize = 0;
        while s <= target_usize {
            let mut k: usize = 0;
            while k <= count && k * marks <= s {
                let prev: i64 = dp[s - k * marks];
                let cur: i64 = next[s] + prev;

                if cur >= modv {
                    next[s] = cur - modv;
                } else {
                    next[s] = cur;
                }

                k = k + 1;
            }
            s = s + 1;
        }

        dp = next;
        ti = ti + 1;
    }

    dp[target_usize]
}
