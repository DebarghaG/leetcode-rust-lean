pub fn min_patches(nums: &[i64], n: i64) -> i64 {
    let mut patches: i64 = 0;
    let mut miss: i64 = 1;
    let mut i: usize = 0;
    let len = nums.len();

    while miss <= n {
        if i < len && nums[i] <= miss {
            miss += nums[i];
            i += 1;
        } else {
            miss += miss;
            patches += 1;
        }
    }

    patches
}
