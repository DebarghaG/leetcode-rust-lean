pub fn max_subarray_length(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n <= 1 {
        return 0;
    }

    // Candidate left endpoints: indices whose value is strictly greater
    // than every value before them.
    let mut left: Vec<i64> = Vec::new();
    left.push(0_i64);

    let mut max_val: i64 = nums[0];
    let mut i: usize = 1;
    while i < n {
        if nums[i] > max_val {
            left.push(i as i64);
            max_val = nums[i];
        }
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut k: usize = left.len();
    let mut j: usize = n;

    while j > 0 {
        j -= 1;

        while k > 0 {
            let idx_i64: i64 = left[k - 1];
            let idx: usize = idx_i64 as usize;

            if nums[idx] > nums[j] {
                let len: i64 = (j as i64) - idx_i64 + 1;
                if len > ans {
                    ans = len;
                }
                k -= 1;
            } else {
                break;
            }
        }
    }

    ans
}
