fn dp_index(l: usize, r: usize, k: usize, n: usize, kdim: usize) -> usize {
    (l * n + r) * kdim + k
}

pub fn remove_boxes(boxes: &[i64]) -> i64 {
    let n = boxes.len();
    if n == 0 {
        return 0;
    }

    let kdim = n + 1;
    let total = n * n * kdim;
    let mut dp: Vec<i64> = Vec::new();
    let mut t = 0usize;
    while t < total {
        dp.push(0);
        t += 1;
    }

    let mut i = 0usize;
    while i < n {
        let mut k = 0usize;
        while k < kdim {
            let s = (k as i64) + 1;
            dp[dp_index(i, i, k, n, kdim)] = s * s;
            k += 1;
        }
        i += 1;
    }

    let mut len = 2usize;
    while len <= n {
        let maxk = n - len;
        let mut l = 0usize;
        while l + len <= n {
            let r = l + len - 1;
            let mut k = 0usize;
            while k <= maxk {
                let s = (k as i64) + 1;
                let mut best = dp[dp_index(l, r - 1, 0, n, kdim)] + s * s;

                let mut p = l;
                while p < r {
                    if boxes[p] == boxes[r] {
                        let mut cand = dp[dp_index(l, p, k + 1, n, kdim)];
                        if p + 1 < r {
                            cand += dp[dp_index(p + 1, r - 1, 0, n, kdim)];
                        }
                        if cand > best {
                            best = cand;
                        }
                    }
                    p += 1;
                }

                dp[dp_index(l, r, k, n, kdim)] = best;
                k += 1;
            }
            l += 1;
        }
        len += 1;
    }

    dp[dp_index(0, n - 1, 0, n, kdim)]
}
