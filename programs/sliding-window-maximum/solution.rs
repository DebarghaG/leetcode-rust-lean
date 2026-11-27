pub fn max_sliding_window(nums: &[i64], k: i64) -> Vec<i64> {
    let n = nums.len();
    let mut out: Vec<i64> = Vec::new();

    if n == 0 || k <= 0 {
        return out;
    }

    let k_usize = k as usize;
    if k_usize > n {
        return out;
    }

    let mut dq: Vec<i64> = Vec::new();
    let mut head: usize = 0;
    let mut i: usize = 0;

    while i < n {
        // Remove indices that are outside the current window [i-k+1, i].
        while head < dq.len() {
            let front_idx = dq[head] as usize;
            if front_idx + k_usize <= i {
                head += 1;
            } else {
                break;
            }
        }

        // Maintain decreasing values in the deque.
        while dq.len() > head {
            let last_pos = dq.len() - 1;
            let last_idx = dq[last_pos] as usize;
            if nums[last_idx] <= nums[i] {
                dq.pop();
            } else {
                break;
            }
        }

        dq.push(i as i64);

        if i + 1 >= k_usize {
            out.push(nums[dq[head] as usize]);
        }

        i += 1;
    }

    out
}
