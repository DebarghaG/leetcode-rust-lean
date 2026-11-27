pub fn minimize_concatenated_length(words: &[Vec<u8>]) -> i64 {
    let n = words.len();
    if n == 0 {
        return 0;
    }

    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < 676 {
        dp.push(inf);
        z += 1;
    }

    let first_len = words[0].len() as i64;
    let f0 = (words[0][0] - b'a') as usize;
    let l0 = (words[0][words[0].len() - 1] - b'a') as usize;
    dp[f0 * 26 + l0] = first_len;

    let mut i: usize = 1;
    while i < n {
        let wlen = words[i].len() as i64;
        let a = (words[i][0] - b'a') as usize;
        let b = (words[i][words[i].len() - 1] - b'a') as usize;

        let mut ndp: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < 676 {
            ndp.push(inf);
            q += 1;
        }

        let mut f: usize = 0;
        while f < 26 {
            let mut l: usize = 0;
            while l < 26 {
                let idx = f * 26 + l;
                let cur = dp[idx];

                if cur != inf {
                    let mut add_append = wlen;
                    if l == a {
                        add_append -= 1;
                    }
                    let new_len_append = cur + add_append;
                    let idx_append = f * 26 + b;
                    if new_len_append < ndp[idx_append] {
                        ndp[idx_append] = new_len_append;
                    }

                    let mut add_prepend = wlen;
                    if b == f {
                        add_prepend -= 1;
                    }
                    let new_len_prepend = cur + add_prepend;
                    let idx_prepend = a * 26 + l;
                    if new_len_prepend < ndp[idx_prepend] {
                        ndp[idx_prepend] = new_len_prepend;
                    }
                }

                l += 1;
            }
            f += 1;
        }

        dp = ndp;
        i += 1;
    }

    let mut ans = inf;
    let mut k: usize = 0;
    while k < 676 {
        if dp[k] < ans {
            ans = dp[k];
        }
        k += 1;
    }

    ans
}
