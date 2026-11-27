pub fn longest_nice_subarray(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut used: i64 = 0;
    let mut best: i64 = 0;

    while right < n {
        let x = nums[right];

        while (used & x) != 0 {
            used = used ^ nums[left];
            left += 1;
        }

        used = used | x;

        let len = (right - left + 1) as i64;
        if len > best {
            best = len;
        }

        right += 1;
    }

    best
}
