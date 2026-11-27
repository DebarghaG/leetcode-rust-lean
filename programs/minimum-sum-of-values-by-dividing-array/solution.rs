pub fn minimum_value_sum(nums: &[i64], andValues: &[i64]) -> i64 {
    let n = nums.len();
    let m = andValues.len();

    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dp_prev: Vec<i64> = Vec::new();
    let mut i = 0;
    while i <= n {
        dp_prev.push(inf);
        i += 1;
    }
    dp_prev[0] = 0;

    let mut g = 0;
    while g < m {
        let target = andValues[g];

        let mut dp_curr: Vec<i64> = Vec::new();
        i = 0;
        while i <= n {
            dp_curr.push(inf);
            i += 1;
        }

        let mut old_vals: Vec<i64> = Vec::new();
        let mut old_bests: Vec<i64> = Vec::new();

        let mut end = 1;
        while end <= n {
            let x = nums[end - 1];

            let mut new_vals: Vec<i64> = Vec::new();
            let mut new_bests: Vec<i64> = Vec::new();

            let mut t = 0;
            while t < old_vals.len() {
                let val = old_vals[t] & x;
                let best = old_bests[t];

                let mut found = false;
                let mut q = 0;
                while q < new_vals.len() {
                    if new_vals[q] == val {
                        if best < new_bests[q] {
                            new_bests[q] = best;
                        }
                        found = true;
                    }
                    q += 1;
                }

                if !found {
                    new_vals.push(val);
                    new_bests.push(best);
                }

                t += 1;
            }

            let val2 = x;
            let best2 = dp_prev[end - 1];

            let mut found2 = false;
            let mut q2 = 0;
            while q2 < new_vals.len() {
                if new_vals[q2] == val2 {
                    if best2 < new_bests[q2] {
                        new_bests[q2] = best2;
                    }
                    found2 = true;
                }
                q2 += 1;
            }

            if !found2 {
                new_vals.push(val2);
                new_bests.push(best2);
            }

            old_vals = new_vals;
            old_bests = new_bests;

            let mut q3 = 0;
            while q3 < old_vals.len() {
                if old_vals[q3] == target {
                    let best = old_bests[q3];
                    if best < inf {
                        let cand = best + x;
                        if cand < dp_curr[end] {
                            dp_curr[end] = cand;
                        }
                    }
                }
                q3 += 1;
            }

            end += 1;
        }

        dp_prev = dp_curr;
        g += 1;
    }

    if dp_prev[n] >= inf / 2 {
        -1
    } else {
        dp_prev[n]
    }
}
