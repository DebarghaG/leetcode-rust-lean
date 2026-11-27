pub fn longest_subsequence(arr: &[i64], difference: i64) -> i64 {
    let n = arr.len();
    if n == 0 {
        return 0;
    }

    // For small inputs, use a position-indexed DP. This avoids allocating
    // a value-sized table for tiny test cases.
    if n <= 2000 {
        let mut dp: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            dp.push(1);
            i += 1;
        }

        let mut ans: i64 = 1;
        i = 0;
        while i < n {
            let x = arr[i];
            let mut j: usize = 0;
            while j < i {
                if x - arr[j] == difference {
                    let cand = dp[j] + 1;
                    if cand > dp[i] {
                        dp[i] = cand;
                    }
                }
                j += 1;
            }
            if dp[i] > ans {
                ans = dp[i];
            }
            i += 1;
        }
        return ans;
    }

    // For larger inputs, values are bounded by the problem constraints:
    // -10000 <= arr[i] <= 10000. Use a fixed offset value table.
    let offset: i64 = 10000;
    let size: usize = 20001;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        dp.push(0);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut k: usize = 0;

    if difference >= 0 {
        let d: usize = difference as usize;
        while k < n {
            let x = arr[k];
            let idx: usize = (x + offset) as usize;

            let mut best: i64 = 1;
            if idx >= d {
                best = dp[idx - d] + 1;
            }

            dp[idx] = best;
            if best > ans {
                ans = best;
            }
            k += 1;
        }
    } else {
        let d: usize = (-difference) as usize;
        while k < n {
            let x = arr[k];
            let idx: usize = (x + offset) as usize;

            let mut best: i64 = 1;
            if idx + d < size {
                best = dp[idx + d] + 1;
            }

            dp[idx] = best;
            if best > ans {
                ans = best;
            }
            k += 1;
        }
    }

    ans
}
