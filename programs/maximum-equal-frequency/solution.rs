pub fn max_equal_freq(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut max_val: usize = 0;
    let mut i: usize = 0;
    while i < n {
        let v = nums[i] as usize;
        if v > max_val {
            max_val = v;
        }
        i += 1;
    }

    let mut count: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < max_val + 2 {
        count.push(0);
        k += 1;
    }

    let mut freq: Vec<i64> = Vec::new();
    k = 0;
    while k < n + 2 {
        freq.push(0);
        k += 1;
    }

    let mut max_freq: i64 = 0;
    let mut ans: i64 = 0;

    i = 0;
    while i < n {
        let x = nums[i] as usize;
        let old = count[x];

        if old > 0 {
            let old_idx = old as usize;
            freq[old_idx] = freq[old_idx] - 1;
        }

        let new_count = old + 1;
        count[x] = new_count;

        let new_idx = new_count as usize;
        freq[new_idx] = freq[new_idx] + 1;

        if new_count > max_freq {
            max_freq = new_count;
        }

        let len = (i as i64) + 1;
        let mut ok = false;

        if max_freq == 1 {
            ok = true;
        } else {
            if freq[max_freq as usize] == 1 {
                let lower = max_freq - 1;
                if freq[lower as usize] * lower + max_freq == len {
                    ok = true;
                }
            }

            if !ok && freq[1] == 1 {
                if freq[max_freq as usize] * max_freq + 1 == len {
                    ok = true;
                }
            }
        }

        if ok {
            ans = len;
        }

        i += 1;
    }

    ans
}
