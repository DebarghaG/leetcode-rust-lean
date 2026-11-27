fn dp_index(i: usize, j: usize, t: usize, n: usize, kmax: usize) -> usize {
    ((i * n + j) * (kmax + 1)) + t
}

pub fn longest_palindromic_subsequence(s: &[u8], k: i64) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let kmax: usize = if k > 0 { k as usize } else { 0 };
    let kk = kmax + 1;
    let total = n * n * kk;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < total {
        dp.push(0);
        z = z + 1;
    }

    let mut i: usize = 0;
    while i < n {
        let mut t: usize = 0;
        while t < kk {
            let idx = dp_index(i, i, t, n, kmax);
            dp[idx] = 1;
            t = t + 1;
        }
        i = i + 1;
    }

    let mut len: usize = 2;
    while len <= n {
        let mut i: usize = 0;
        while i + len <= n {
            let j = i + len - 1;

            let a = s[i] as i64;
            let b = s[j] as i64;
            let diff = if a > b { a - b } else { b - a };
            let other = 26 - diff;
            let cost64 = if diff < other { diff } else { other };
            let cost = cost64 as usize;

            let mut t: usize = 0;
            while t < kk {
                let idx1 = dp_index(i + 1, j, t, n, kmax);
                let v1 = dp[idx1];

                let idx2 = dp_index(i, j - 1, t, n, kmax);
                let v2 = dp[idx2];

                let mut best = v1;
                if v2 > best {
                    best = v2;
                }

                if t >= cost {
                    let mut inside: i64 = 0;
                    if len > 2 {
                        let idx3 = dp_index(i + 1, j - 1, t - cost, n, kmax);
                        inside = dp[idx3];
                    }
                    let candidate = inside + 2;
                    if candidate > best {
                        best = candidate;
                    }
                }

                let idx = dp_index(i, j, t, n, kmax);
                dp[idx] = best;
                t = t + 1;
            }

            i = i + 1;
        }
        len = len + 1;
    }

    let answer_idx = dp_index(0, n - 1, kmax, n, kmax);
    dp[answer_idx]
}
