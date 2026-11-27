pub fn maximum_score(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut start: usize = 0;
    let mut pos: i64 = 0;
    while pos < k {
        start += 1;
        pos += 1;
    }

    let mut left = start;
    let mut right = start;
    let mut cur_min = nums[start];
    let mut best = cur_min;
    let mut width: i64 = 1;

    while left > 0 || right + 1 < n {
        if left == 0 {
            right += 1;
            if nums[right] < cur_min {
                cur_min = nums[right];
            }
        } else if right + 1 == n {
            left -= 1;
            if nums[left] < cur_min {
                cur_min = nums[left];
            }
        } else {
            let left_value = nums[left - 1];
            let right_value = nums[right + 1];

            if left_value >= right_value {
                left -= 1;
                if nums[left] < cur_min {
                    cur_min = nums[left];
                }
            } else {
                right += 1;
                if nums[right] < cur_min {
                    cur_min = nums[right];
                }
            }
        }

        width += 1;
        let score = cur_min * width;
        if score > best {
            best = score;
        }
    }

    best
}
