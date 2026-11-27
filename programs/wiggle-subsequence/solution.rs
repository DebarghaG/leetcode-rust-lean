pub fn wiggle_max_length(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let mut up: i64 = 1;
    let mut down: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if nums[i] > nums[i - 1] {
            up = down + 1;
        } else if nums[i] < nums[i - 1] {
            down = up + 1;
        }
        i += 1;
    }

    if up > down {
        up
    } else {
        down
    }
}
