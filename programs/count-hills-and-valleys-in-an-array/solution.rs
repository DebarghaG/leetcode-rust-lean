pub fn count_hill_valley(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut count: i64 = 0;
    let mut i: usize = 1;

    while i + 1 < n {
        if nums[i] == nums[i - 1] {
            i += 1;
        } else {
            let mut r: usize = i;
            while r + 1 < n && nums[r + 1] == nums[i] {
                r += 1;
            }

            if r + 1 < n {
                let left = nums[i - 1];
                let right = nums[r + 1];
                let cur = nums[i];

                if (cur > left && cur > right) || (cur < left && cur < right) {
                    count += 1;
                }
            }

            i = r + 1;
        }
    }

    count
}
