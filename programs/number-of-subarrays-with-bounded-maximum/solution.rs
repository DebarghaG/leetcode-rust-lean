pub fn num_subarray_bounded_max(nums: &[i64], left: i64, right: i64) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;
    let mut last_bad: i64 = -1;
    let mut last_good: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];

        if x > right {
            last_bad = i as i64;
        } else if x >= left {
            last_good = i as i64;
        }

        if last_good > last_bad {
            ans += last_good - last_bad;
        }

        i += 1;
    }

    ans
}
