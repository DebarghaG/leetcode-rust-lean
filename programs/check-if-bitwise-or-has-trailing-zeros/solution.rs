pub fn has_trailing_zeros(nums: &[i64]) -> bool {
    let mut even_count: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        if nums[i] % 2 == 0 {
            even_count += 1;
        }
        i += 1;
    }

    even_count >= 2
}
