pub fn count_k_difference(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let mut diff = nums[i] - nums[j];
            if diff < 0 {
                diff = -diff;
            }
            if diff == k {
                count += 1;
            }
            j += 1;
        }
        i += 1;
    }

    count
}
