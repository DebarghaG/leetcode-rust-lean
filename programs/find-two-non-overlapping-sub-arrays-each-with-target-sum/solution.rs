pub fn min_sum_of_lengths(arr: &[i64], target: i64) -> i64 {
    let n = arr.len();
    let inf: i64 = 1_000_000_000;

    let mut ans: i64 = inf;
    let mut best_so_far: i64 = inf;
    let mut prefix_min: Vec<i64> = Vec::new();

    let mut start: usize = 0;
    let mut cur: i64 = 0;
    let mut r: usize = 0;

    while r < n {
        cur += arr[r];

        while cur > target && start <= r {
            cur -= arr[start];
            start += 1;
        }

        let mut len_here: i64 = inf;

        if cur == target {
            let len = (r - start + 1) as i64;
            len_here = len;

            if start > 0 {
                let previous_best = prefix_min[start - 1];
                if previous_best < inf {
                    let total = previous_best + len;
                    if total < ans {
                        ans = total;
                    }
                }
            }
        }

        if len_here < best_so_far {
            best_so_far = len_here;
        }

        prefix_min.push(best_so_far);
        r += 1;
    }

    if ans == inf { -1 } else { ans }
}
