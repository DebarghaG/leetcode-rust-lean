pub fn longest_palindrome_subseq(s: &[u8]) -> i64 {
    let n = s.len();
    if n < 2 {
        return 0;
    }

    let alpha: usize = 26;
    let total = n * n * alpha;
    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dp.push(0);
        i += 1;
    }

    let mut l: usize = n;
    while l > 0 {
        l -= 1;

        let mut r: usize = l + 1;
        while r < n {
            let mut c: usize = 0;
            while c < alpha {
                let mut best: i64 = 0;

                let v1 = dp[((l + 1) * n + r) * alpha + c];
                if v1 > best {
                    best = v1;
                }

                let v2 = dp[(l * n + (r - 1)) * alpha + c];
                if v2 > best {
                    best = v2;
                }

                let target: u8 = b'a' + (c as u8);
                if s[l] == target && s[r] == target {
                    let mut inner: i64 = 0;
                    if l + 1 <= r - 1 {
                        let mut d: usize = 0;
                        while d < alpha {
                            if d != c {
                                let v = dp[((l + 1) * n + (r - 1)) * alpha + d];
                                if v > inner {
                                    inner = v;
                                }
                            }
                            d += 1;
                        }
                    }

                    let cand = inner + 2;
                    if cand > best {
                        best = cand;
                    }
                }

                dp[(l * n + r) * alpha + c] = best;
                c += 1;
            }
            r += 1;
        }
    }

    let mut ans: i64 = 0;
    let mut c: usize = 0;
    while c < alpha {
        let v = dp[(n - 1) * alpha + c];
        if v > ans {
            ans = v;
        }
        c += 1;
    }

    ans
}
