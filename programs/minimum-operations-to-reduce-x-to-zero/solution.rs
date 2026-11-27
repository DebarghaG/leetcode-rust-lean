pub fn min_operations(nums: &[i64], x: i64) -> i64 {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let target = total - x;
    if target < 0 {
        return -1;
    }

    if target == 0 {
        return n as i64;
    }

    let mut best: i64 = -1;
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut current: i64 = 0;

    while right < n {
        current += nums[right];

        while current > target && left <= right {
            current -= nums[left];
            left += 1;
        }

        if current == target {
            if left <= right {
                let len = (right - left + 1) as i64;
                if len > best {
                    best = len;
                }
            }
        }

        right += 1;
    }

    if best == -1 {
        -1
    } else {
        n as i64 - best
    }
}
