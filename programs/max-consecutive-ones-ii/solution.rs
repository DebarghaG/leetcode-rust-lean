pub fn find_max_consecutive_ones(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut zeros: i64 = 0;
    let mut best: i64 = 0;

    while right < n {
        if nums[right] == 0 {
            zeros += 1;
        }

        while zeros > 1 {
            if nums[left] == 0 {
                zeros -= 1;
            }
            left += 1;
        }

        let current = (right - left + 1) as i64;
        if current > best {
            best = current;
        }

        right += 1;
    }

    best
}
