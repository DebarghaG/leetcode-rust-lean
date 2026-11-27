pub fn is_array_special(nums: &[i64]) -> bool {
    let n = nums.len();
    if n <= 1 {
        return true;
    }

    let mut i: usize = 1;
    while i < n {
        let prev_parity = nums[i - 1] % 2;
        let curr_parity = nums[i] % 2;
        if prev_parity == curr_parity {
            return false;
        }
        i += 1;
    }

    true
}
