pub fn longest_subarray(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut max_val = nums[0];
    let mut i = 1;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut best = 0;
    let mut cur = 0;
    let mut j = 0;
    while j < n {
        if nums[j] == max_val {
            cur += 1;
            if cur > best {
                best = cur;
            }
        } else {
            cur = 0;
        }
        j += 1;
    }

    best
}
