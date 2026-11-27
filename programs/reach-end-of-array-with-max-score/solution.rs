pub fn find_maximum_score(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut best = nums[0];
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i + 1 < n {
        if nums[i] > best {
            best = nums[i];
        }
        total = total + best;
        i = i + 1;
    }

    total
}
