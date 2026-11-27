pub fn smallest_equal(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut i: usize = 0;
    while i < n {
        let r = (i as i64) % 10;
        if r == nums[i] {
            return i as i64;
        }
        i += 1;
    }
    -1
}
