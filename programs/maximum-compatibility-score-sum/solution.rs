pub fn max_compatibility_sum(students: &[Vec<i64>], mentors: &[Vec<i64>]) -> i64 {
    let m = students.len();
    if m == 0 {
        return 0;
    }

    let n = students[0].len();
    if n == 0 {
        return 0;
    }

    let mut score: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < m {
            let mut c: i64 = 0;
            let mut k = 0;
            while k < n {
                if students[i][k] == mentors[j][k] {
                    c += 1;
                }
                k += 1;
            }
            score.push(c);
            j += 1;
        }
        i += 1;
    }

    let total: usize = 1usize << m;
    let mut dp: Vec<i64> = Vec::new();
    let mut idx = 0;
    while idx < total {
        dp.push(-1);
        idx += 1;
    }
    dp[0] = 0;

    let mut mask: usize = 0;
    while mask < total {
        if dp[mask] >= 0 {
            let mut s: usize = 0;
            let mut x = mask;
            while x > 0 {
                if (x & 1usize) == 1usize {
                    s += 1;
                }
                x = x >> 1;
            }

            if s < m {
                let mut j: usize = 0;
                while j < m {
                    let bit: usize = 1usize << j;
                    if (mask & bit) == 0 {
                        let next_mask = mask | bit;
                        let candidate = dp[mask] + score[s * m + j];
                        if candidate > dp[next_mask] {
                            dp[next_mask] = candidate;
                        }
                    }
                    j += 1;
                }
            }
        }
        mask += 1;
    }

    dp[total - 1]
}
