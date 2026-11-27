pub fn sum_of_unique(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut count: i64 = 0;
        let mut j: usize = 0;

        while j < n {
            if nums[j] == nums[i] {
                count += 1;
            }
            j += 1;
        }

        if count == 1 {
            sum += nums[i];
        }

        i += 1;
    }

    sum
}
