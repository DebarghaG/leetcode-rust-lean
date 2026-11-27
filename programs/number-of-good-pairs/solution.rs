pub fn num_identical_pairs(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            if nums[i] == nums[j] {
                count += 1;
            }
            j += 1;
        }
        i += 1;
    }

    count
}
