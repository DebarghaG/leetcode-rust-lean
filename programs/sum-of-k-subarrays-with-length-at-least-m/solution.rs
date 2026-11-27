pub fn max_sum(nums: &[i64], k: i64, m: i64) -> i64 {
    let n: usize = nums.len();
    let kk: usize = k as usize;
    let mm: usize = m as usize;
    let sentinel: i64 = -20000000;

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);
    let mut idx: usize = 0;
    while idx < n {
        let next_sum: i64 = prefix[idx] + nums[idx];
        prefix.push(next_sum);
        idx += 1;
    }

    let mut dp_prev: Vec<i64> = Vec::new();
    idx = 0;
    while idx <= n {
        dp_prev.push(0);
        idx += 1;
    }

    let mut count: usize = 1;
    while count <= kk {
        let mut dp_cur: Vec<i64> = Vec::new();
        idx = 0;
        while idx <= n {
            dp_cur.push(sentinel);
            idx += 1;
        }

        let mut best: i64 = sentinel;
        idx = 1;
        while idx <= n {
            if idx >= mm {
                let start: usize = idx - mm;
                let val: i64 = dp_prev[start] - prefix[start];
                if val > best {
                    best = val;
                }
            }

            let candidate: i64 = best + prefix[idx];
            let skip: i64 = dp_cur[idx - 1];
            if skip > candidate {
                dp_cur[idx] = skip;
            } else {
                dp_cur[idx] = candidate;
            }

            idx += 1;
        }

        dp_prev = dp_cur;
        count += 1;
    }

    dp_prev[n]
}
