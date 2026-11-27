pub fn minimum_mountain_removals(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }

    let mut left: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        left.push(1);
        i += 1;
    }

    i = 0;
    while i < n {
        let mut j = 0;
        while j < i {
            if nums[j] < nums[i] && left[j] + 1 > left[i] {
                left[i] = left[j] + 1;
            }
            j += 1;
        }
        i += 1;
    }

    let mut right: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        right.push(1);
        i += 1;
    }

    i = n;
    while i > 0 {
        i -= 1;
        let mut j = i + 1;
        while j < n {
            if nums[j] < nums[i] && right[j] + 1 > right[i] {
                right[i] = right[j] + 1;
            }
            j += 1;
        }
    }

    let mut best: i64 = 0;
    i = 0;
    while i < n {
        if left[i] >= 2 && right[i] >= 2 {
            let length = left[i] + right[i] - 1;
            if length > best {
                best = length;
            }
        }
        i += 1;
    }

    let n_i64 = n as i64;
    n_i64 - best
}
