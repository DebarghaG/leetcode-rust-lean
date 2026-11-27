pub fn longest_monotonic_subarray(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 1;
    let mut inc: i64 = 1;
    let mut dec: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if nums[i] > nums[i - 1] {
            inc = inc + 1;
            dec = 1;
        } else if nums[i] < nums[i - 1] {
            dec = dec + 1;
            inc = 1;
        } else {
            inc = 1;
            dec = 1;
        }

        if inc > best {
            best = inc;
        }
        if dec > best {
            best = dec;
        }

        i = i + 1;
    }

    best
}
