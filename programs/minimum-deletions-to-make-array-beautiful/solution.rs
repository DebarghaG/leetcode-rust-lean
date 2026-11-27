pub fn min_deletion(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut i: usize = 0;
    let mut kept: i64 = 0;
    let mut last: i64 = 0;
    let mut deleted: i64 = 0;

    while i < n {
        if kept % 2 == 0 {
            last = nums[i];
            kept += 1;
        } else if nums[i] != last {
            last = nums[i];
            kept += 1;
        } else {
            deleted += 1;
        }
        i += 1;
    }

    if kept % 2 == 1 {
        deleted += 1;
    }

    deleted
}
