pub fn remove_duplicates(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    let mut k: i64 = 1;
    let mut i: usize = 1;
    while i < n {
        if nums[i] != nums[i - 1] {
            k += 1;
        }
        i += 1;
    }
    k
}
