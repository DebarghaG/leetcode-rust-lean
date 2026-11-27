pub fn minimum_swaps(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n <= 1 {
        return 0;
    }

    let mut min_val: i64 = nums[0];
    let mut max_val: i64 = nums[0];
    let mut min_idx: usize = 0;
    let mut max_idx: usize = 0;

    let mut i: usize = 1;
    while i < n {
        if nums[i] < min_val {
            min_val = nums[i];
            min_idx = i;
        }
        if nums[i] >= max_val {
            max_val = nums[i];
            max_idx = i;
        }
        i += 1;
    }

    let moved_min: usize = min_idx;
    let moved_max: usize = n - 1 - max_idx;
    let mut ans: i64 = (moved_min + moved_max) as i64;

    if min_idx > max_idx {
        ans -= 1;
    }

    ans
}
