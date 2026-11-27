pub fn minimum_sum_subarray(nums: &[i64], l: i64, r: i64) -> i64 {
    let n = nums.len();
    let mut best: i64 = -1;

    let mut start: usize = 0;
    while start < n {
        let mut sum: i64 = 0;
        let mut end: usize = start;

        while end < n {
            sum = sum + nums[end];
            let length = (end - start + 1) as i64;

            if length >= l && length <= r && sum > 0 {
                if best == -1 || sum < best {
                    best = sum;
                }
            }

            end = end + 1;
        }

        start = start + 1;
    }

    best
}
