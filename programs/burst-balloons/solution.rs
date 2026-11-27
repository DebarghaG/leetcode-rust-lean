pub fn max_coins(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    let m: usize = n + 2;

    let mut a: Vec<i64> = Vec::new();
    a.push(1);
    let mut p: usize = 0;
    while p < n {
        a.push(nums[p]);
        p += 1;
    }
    a.push(1);

    let total: usize = m * m;
    let mut dp: Vec<i64> = Vec::new();
    let mut q: usize = 0;
    while q < total {
        dp.push(0);
        q += 1;
    }

    let mut len: usize = 2;
    while len < m {
        let mut i: usize = 0;
        while i + len < m {
            let j: usize = i + len;
            let mut best: i64 = 0;
            let mut k: usize = i + 1;
            while k < j {
                let left: i64 = dp[i * m + k];
                let right: i64 = dp[k * m + j];
                let coins: i64 = a[i] * a[k] * a[j];
                let cur: i64 = left + right + coins;
                if cur > best {
                    best = cur;
                }
                k += 1;
            }
            dp[i * m + j] = best;
            i += 1;
        }
        len += 1;
    }

    dp[m - 1]
}
