fn merge_sort(values: &mut Vec<i64>) {
    let len = values.len();
    if len <= 1 {
        return;
    }

    let mut buffer: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < len {
        buffer.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < len {
        let mut left: usize = 0;

        while left < len {
            let mid: usize;
            if left + width < len {
                mid = left + width;
            } else {
                mid = len;
            }

            let right: usize;
            if left + width + width < len {
                right = left + width + width;
            } else {
                right = len;
            }

            let mut a: usize = left;
            let mut b: usize = mid;
            let mut k: usize = left;

            while a < mid && b < right {
                if values[a] <= values[b] {
                    buffer[k] = values[a];
                    a += 1;
                } else {
                    buffer[k] = values[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                buffer[k] = values[a];
                a += 1;
                k += 1;
            }

            while b < right {
                buffer[k] = values[b];
                b += 1;
                k += 1;
            }

            left = right;
        }

        let mut t: usize = 0;
        while t < len {
            values[t] = buffer[t];
            t += 1;
        }

        width = width + width;
    }
}

pub fn longest_increasing_path(matrix: &[Vec<i64>]) -> i64 {
    let m = matrix.len();
    if m == 0 {
        return 0;
    }

    let n = matrix[0].len();
    if n == 0 {
        return 0;
    }

    let total = m * n;
    let base: i64 = 1000000;

    let mut keys: Vec<i64> = Vec::new();

    let mut r: usize = 0;
    while r < m {
        let row = &matrix[r];
        let mut c: usize = 0;
        while c < n {
            let idx = r * n + c;
            let key = row[c] * base + (idx as i64);
            keys.push(key);
            c += 1;
        }
        r += 1;
    }

    merge_sort(&mut keys);

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dp.push(1);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut p: usize = 0;

    while p < total {
        let key = keys[p];
        let val = key / base;
        let idx_i = key % base;
        let idx = idx_i as usize;

        let r = idx / n;
        let c = idx % n;

        let mut best: i64 = 1;
        let currow = &matrix[r];

        if c > 0 {
            let ni = idx - 1;
            if currow[c - 1] < val {
                let cand = dp[ni] + 1;
                if cand > best {
                    best = cand;
                }
            }
        }

        if c + 1 < n {
            let ni = idx + 1;
            if currow[c + 1] < val {
                let cand = dp[ni] + 1;
                if cand > best {
                    best = cand;
                }
            }
        }

        if r > 0 {
            let ni = idx - n;
            let uprow = &matrix[r - 1];
            if uprow[c] < val {
                let cand = dp[ni] + 1;
                if cand > best {
                    best = cand;
                }
            }
        }

        if r + 1 < m {
            let ni = idx + n;
            let downrow = &matrix[r + 1];
            if downrow[c] < val {
                let cand = dp[ni] + 1;
                if cand > best {
                    best = cand;
                }
            }
        }

        dp[idx] = best;

        if best > ans {
            ans = best;
        }

        p += 1;
    }

    ans
}
