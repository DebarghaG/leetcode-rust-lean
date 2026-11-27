pub fn remove_element(nums: &[i64], val: i64) -> i64 {
    let mut k: i64 = 0;
    let mut i: usize = 0;
    let n: usize = nums.len();

    while i < n {
        if nums[i] != val {
            k += 1;
        }
        i += 1;
    }

    k
}
