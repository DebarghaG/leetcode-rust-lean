pub fn max_profit_assignment(difficulty: &[i64], profit: &[i64], worker: &[i64]) -> i64 {
    let n = difficulty.len();
    let m = worker.len();

    let mut diff: Vec<i64> = Vec::new();
    let mut prof: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        diff.push(difficulty[i]);
        prof.push(profit[i]);
        i += 1;
    }

    let mut tmp_d: Vec<i64> = Vec::new();
    let mut tmp_p: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        tmp_d.push(0);
        tmp_p.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + 2 * width;
            if right > n {
                right = n;
            }

            let mut a: usize = left;
            let mut b: usize = mid;
            let mut k: usize = left;

            while a < mid && b < right {
                if diff[a] <= diff[b] {
                    tmp_d[k] = diff[a];
                    tmp_p[k] = prof[a];
                    a += 1;
                } else {
                    tmp_d[k] = diff[b];
                    tmp_p[k] = prof[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                tmp_d[k] = diff[a];
                tmp_p[k] = prof[a];
                a += 1;
                k += 1;
            }

            while b < right {
                tmp_d[k] = diff[b];
                tmp_p[k] = prof[b];
                b += 1;
                k += 1;
            }

            left += 2 * width;
        }

        i = 0;
        while i < n {
            diff[i] = tmp_d[i];
            prof[i] = tmp_p[i];
            i += 1;
        }

        width = width * 2;
    }

    let mut work: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        work.push(worker[i]);
        i += 1;
    }

    let mut tmp_w: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        tmp_w.push(0);
        i += 1;
    }

    width = 1;
    while width < m {
        let mut left: usize = 0;
        while left < m {
            let mut mid: usize = left + width;
            if mid > m {
                mid = m;
            }

            let mut right: usize = left + 2 * width;
            if right > m {
                right = m;
            }

            let mut a: usize = left;
            let mut b: usize = mid;
            let mut k: usize = left;

            while a < mid && b < right {
                if work[a] <= work[b] {
                    tmp_w[k] = work[a];
                    a += 1;
                } else {
                    tmp_w[k] = work[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                tmp_w[k] = work[a];
                a += 1;
                k += 1;
            }

            while b < right {
                tmp_w[k] = work[b];
                b += 1;
                k += 1;
            }

            left += 2 * width;
        }

        i = 0;
        while i < m {
            work[i] = tmp_w[i];
            i += 1;
        }

        width = width * 2;
    }

    let mut ans: i64 = 0;
    let mut j: usize = 0;
    let mut best: i64 = 0;

    i = 0;
    while i < m {
        let w = work[i];

        while j < n && diff[j] <= w {
            if prof[j] > best {
                best = prof[j];
            }
            j += 1;
        }

        ans += best;
        i += 1;
    }

    ans
}
