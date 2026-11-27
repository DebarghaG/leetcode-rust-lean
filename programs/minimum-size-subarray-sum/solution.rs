pub fn min_sub_array_len(target: i64, nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut left: usize = 0;
    let mut sum: i64 = 0;
    let mut best: i64 = 0;
    let mut cur_len: i64 = 0;

    for right in 0..n {
        sum += nums[right];
        cur_len += 1;

        while sum >= target {
            if best == 0 || cur_len < best {
                best = cur_len;
            }
            sum -= nums[left];
            left += 1;
            cur_len -= 1;
        }
    }

    best
}
