pub fn max_total_reward(rewardValues: &[i64]) -> i64 {
    let n = rewardValues.len();
    if n == 0 {
        return 0;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut max_val: i64 = 0;

    while i < n {
        let v = rewardValues[i];
        vals.push(v);
        if v > max_val {
            max_val = v;
        }
        i += 1;
    }

    // Selection sort in ascending order.
    let m = vals.len();
    let mut a: usize = 0;
    while a < m {
        let mut best: usize = a;
        let mut b: usize = a + 1;
        while b < m {
            if vals[b] < vals[best] {
                best = b;
            }
            b += 1;
        }
        let tmp = vals[a];
        vals[a] = vals[best];
        vals[best] = tmp;
        a += 1;
    }

    // Any achievable final total is less than 2 * max_val.
    let size: usize = (max_val as usize) * 2 + 1;
    let mut dp: Vec<bool> = Vec::new();
    let mut p: usize = 0;
    while p < size {
        dp.push(false);
        p += 1;
    }
    dp[0] = true;

    let mut k: usize = 0;
    while k < vals.len() {
        let v: usize = vals[k] as usize;

        let mut x: usize = 0;
        while x < v {
            if dp[x] {
                let nx: usize = x + v;
                if nx < dp.len() {
                    dp[nx] = true;
                }
            }
            x += 1;
        }

        k += 1;
    }

    let mut ans: i64 = 0;
    let mut s: usize = 0;
    while s < dp.len() {
        if dp[s] {
            ans = s as i64;
        }
        s += 1;
    }

    ans
}
