pub fn find_subarrays(nums: &[i64]) -> bool {
    let n = nums.len();
    let mut found: bool = false;
    let mut i: usize = 0;
    while i + 1 < n {
        let sum1 = nums[i] + nums[i + 1];
        let mut j: usize = i + 1;
        while j + 1 < n {
            let sum2 = nums[j] + nums[j + 1];
            if sum1 == sum2 {
                found = true;
                break;
            }
            j += 1;
        }
        if found {
            break;
        }
        i += 1;
    }
    found
}
