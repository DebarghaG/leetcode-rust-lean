pub fn min_valid_strings(words: &[Vec<u8>], target: &[u8]) -> i64 {
    let n: usize = target.len();
    if n == 0 {
        return 0;
    }

    let mut best: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        best.push(0i64);
        i += 1;
    }

    let word_count: usize = words.len();
    let mut wi: usize = 0;
    while wi < word_count {
        let w = &words[wi];
        let wlen: usize = w.len();

        if wlen > 0 {
            let mut s: Vec<u8> = Vec::new();
            let mut p: usize = 0;
            while p < wlen {
                s.push(w[p]);
                p += 1;
            }
            s.push(0u8);
            p = 0;
            while p < n {
                s.push(target[p]);
                p += 1;
            }

            let total: usize = s.len();
            let mut z: Vec<i64> = Vec::new();
            p = 0;
            while p < total {
                z.push(0i64);
                p += 1;
            }

            let mut l: usize = 0;
            let mut r: usize = 0;
            let mut idx: usize = 1;
            while idx < total {
                let mut zi: i64 = 0;
                if idx < r {
                    zi = z[idx - l];
                    let rem: i64 = (r - idx) as i64;
                    if zi > rem {
                        zi = rem;
                    }
                }

                while idx + (zi as usize) < total
                    && s[zi as usize] == s[idx + (zi as usize)]
                {
                    zi += 1;
                }

                z[idx] = zi;
                let idx_end: usize = idx + (zi as usize);
                if idx_end > r {
                    l = idx;
                    r = idx_end;
                }
                idx += 1;
            }

            let offset: usize = wlen + 1;
            let wlen_i64: i64 = wlen as i64;
            p = 0;
            while p < n {
                let val: i64 = z[offset + p];
                let capped: i64 = if val > wlen_i64 { wlen_i64 } else { val };
                if capped > best[p] {
                    best[p] = capped;
                }
                p += 1;
            }
        }

        wi += 1;
    }

    if best[0] == 0 {
        return -1;
    }

    let mut jumps: i64 = 0;
    let mut current_end: usize = 0;
    let mut scan_start: usize = 0;
    let mut farthest: usize = 0;

    while current_end < n {
        jumps += 1;

        let mut p: usize = scan_start;
        while p <= current_end && p < n {
            let reach_i64: i64 = (p as i64) + best[p];
            let reach: usize = if reach_i64 > (n as i64) {
                n
            } else {
                reach_i64 as usize
            };

            if reach > farthest {
                farthest = reach;
            }
            p += 1;
        }

        if farthest <= current_end {
            return -1;
        }

        scan_start = current_end + 1;
        current_end = if farthest > n { n } else { farthest };
    }

    jumps
}
