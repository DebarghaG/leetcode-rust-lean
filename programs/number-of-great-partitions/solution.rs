pub fn count_partitions(nums: &[i64], k: i64) -> i64 {
    let modv: i64 = 1000000007;
    let n: usize = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    if total < 2 * k {
        return 0;
    }

    let kk: usize = k as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i2: usize = 0;
    while i2 < kk {
        dp.push(0);
        i2 += 1;
    }
    dp[0] = 1;

    let mut idx: usize = 0;
    while idx < n {
        let x: i64 = nums[idx];
        if x < k {
            let xx: usize = x as usize;
            let mut j: usize = kk;
            while j > xx {
                j -= 1;
                dp[j] = (dp[j] + dp[j - xx]) % modv;
            }
        }
        idx += 1;
    }

    let mut less: i64 = 0;
    let mut t: usize = 0;
    while t < kk {
        less = (less + dp[t]) % modv;
        t += 1;
    }

    let mut pow2: i64 = 1;
    let mut e: usize = 0;
    while e < n {
        pow2 = (pow2 * 2) % modv;
        e += 1;
    }

    let twice: i64 = (2 * less) % modv;
    let mut ans: i64 = pow2 - twice;
    if ans < 0 {
        ans += modv;
    }

    ans
}
