pub fn count_k_reducible_numbers(s: &[u8], k: i64) -> i64 {
    let modv: i64 = 1000000007;
    let n_len: usize = s.len();
    let maxc: usize = n_len;

    let mut steps: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c <= maxc {
        if c <= 1 {
            steps.push(0);
        } else {
            let pc: usize = popcount_usize(c);
            let v: i64 = steps[pc] + 1;
            steps.push(v);
        }
        c += 1;
    }

    let mut comb: Vec<Vec<i64>> = Vec::new();
    let mut n: usize = 0;
    while n <= maxc {
        if n == 0 {
            let mut row: Vec<i64> = Vec::new();
            row.push(1);
            comb.push(row);
        } else {
            let mut row: Vec<i64> = Vec::new();
            row.push(1);

            let mut b: usize = 1;
            while b < n {
                let left: i64 = comb[n - 1][b - 1];
                let right: i64 = comb[n - 1][b];
                let val: i64 = (left + right) % modv;
                row.push(val);
                b += 1;
            }

            row.push(1);
            comb.push(row);
        }
        n += 1;
    }

    let limit: i64 = k - 1;
    let mut ans: i64 = 0;
    let mut ones: usize = 0;
    let mut pos: usize = 0;

    while pos < n_len {
        if s[pos] == b'1' {
            let rem: usize = n_len - pos - 1;
            let mut r: usize = 0;

            while r <= rem {
                let total: usize = ones + r;
                if total >= 1 && total <= maxc && steps[total] <= limit {
                    ans = (ans + comb[rem][r]) % modv;
                }
                r += 1;
            }

            ones += 1;
        }
        pos += 1;
    }

    ans % modv
}

fn popcount_usize(mut x: usize) -> usize {
    let mut count: usize = 0;
    while x > 0 {
        if x % 2 == 1 {
            count += 1;
        }
        x = x / 2;
    }
    count
}
