pub fn find_length_of_lcis(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 1;
    }

    let mut best: i64 = 1;
    let mut current: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if nums[i] > nums[i - 1] {
            current += 1;
        } else {
            current = 1;
        }

        if current > best {
            best = current;
        }

        i += 1;
    }

    best
}
