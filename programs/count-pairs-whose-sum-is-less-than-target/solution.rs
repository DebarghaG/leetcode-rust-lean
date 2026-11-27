pub fn count_pairs(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;

        while j < n {
            if nums[i] + nums[j] < target {
                count += 1;
            }
            j += 1;
        }

        i += 1;
    }

    count
}
