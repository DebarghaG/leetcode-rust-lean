pub fn min_cut(s: &[u8]) -> i64 {
    let n = s.len();
    if n <= 1 {
        return 0;
    }

    let mut pal: Vec<Vec<bool>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut row: Vec<bool> = Vec::new();
        let mut j = 0usize;
        while j < n {
            row.push(false);
            j += 1;
        }
        pal.push(row);
        i += 1;
    }

    i = 0usize;
    while i < n {
        pal[i][i] = true;
        i += 1;
    }

    let mut length = 2usize;
    while length <= n {
        let mut l = 0usize;
        while l + length <= n {
            let r = l + length - 1;
            if s[l] == s[r] {
                if length == 2 {
                    pal[l][r] = true;
                } else {
                    if pal[l + 1][r - 1] {
                        pal[l][r] = true;
                    }
                }
            }
            l += 1;
        }
        length += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut k = 0usize;
    while k <= n {
        dp.push(0i64);
        k += 1;
    }

    let mut end = 1usize;
    while end <= n {
        let mut best: i64 = 1000000000i64;
        let r = end - 1;
        let mut start = 0usize;

        while start < end {
            if pal[start][r] {
                let cand: i64;
                if start == 0 {
                    cand = 0i64;
                } else {
                    cand = dp[start] + 1i64;
                }

                if cand < best {
                    best = cand;
                }
            }
            start += 1;
        }

        dp[end] = best;
        end += 1;
    }

    dp[n]
}
