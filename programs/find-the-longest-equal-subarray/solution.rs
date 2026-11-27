pub fn longest_equal_subarray(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut idx = 0;
    while idx < n {
        order.push(idx as i64);
        idx += 1;
    }

    let mut temp: Vec<i64> = Vec::new();
    idx = 0;
    while idx < n {
        temp.push(0);
        idx += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let width2 = width + width;
        let mut start: usize = 0;

        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }
            let mut end = start + width2;
            if end > n {
                end = n;
            }

            let mut i = start;
            let mut j = mid;
            let mut t = start;

            while i < mid && j < end {
                let vi = nums[order[i] as usize];
                let vj = nums[order[j] as usize];
                if vj < vi {
                    temp[t] = order[j];
                    j += 1;
                } else {
                    temp[t] = order[i];
                    i += 1;
                }
                t += 1;
            }

            while i < mid {
                temp[t] = order[i];
                i += 1;
                t += 1;
            }

            while j < end {
                temp[t] = order[j];
                j += 1;
                t += 1;
            }

            start = end;
        }

        let mut c = 0;
        while c < n {
            order[c] = temp[c];
            c += 1;
        }

        width = width2;
    }

    let mut best: i64 = 0;
    let mut g_start: usize = 0;

    while g_start < n {
        let group_value = nums[order[g_start] as usize];
        let mut g_end = g_start + 1;

        while g_end < n && nums[order[g_end] as usize] == group_value {
            g_end += 1;
        }

        let mut left = g_start;
        let mut r = g_start;

        while r < g_end {
            while order[r] - order[left] - ((r - left) as i64) > k {
                left += 1;
            }

            let len = (r - left + 1) as i64;
            if len > best {
                best = len;
            }

            r += 1;
        }

        g_start = g_end;
    }

    best
}
