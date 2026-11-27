pub fn sum_of_good_numbers(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let k_usize = k as usize;
    let mut sum = 0i64;
    let mut i = 0usize;

    while i < n {
        let mut good = true;

        if i >= k_usize {
            let left = i - k_usize;
            if nums[i] <= nums[left] {
                good = false;
            }
        }

        if good && i + k_usize < n {
            let right = i + k_usize;
            if nums[i] <= nums[right] {
                good = false;
            }
        }

        if good {
            sum = sum + nums[i];
        }

        i += 1;
    }

    sum
}
