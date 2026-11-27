pub fn can_split_array(nums: &[i64], m: i64) -> bool {
    let n = nums.len();
    if n <= 2 {
        return true;
    }

    let mut i: usize = 0;
    while i + 1 < n {
        if nums[i] + nums[i + 1] >= m {
            return true;
        }
        i += 1;
    }

    false
}
