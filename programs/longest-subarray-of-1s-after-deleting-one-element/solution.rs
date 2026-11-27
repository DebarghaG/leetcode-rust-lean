pub fn longest_subarray(nums: &[i64]) -> i64 {
    let n = nums.len();
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

        let window_len = (right - left + 1) as i64;
        if window_len > best {
            best = window_len;
        }

        right += 1;
    }

    if best > 0 {
        best - 1
    } else {
        0
    }
}
