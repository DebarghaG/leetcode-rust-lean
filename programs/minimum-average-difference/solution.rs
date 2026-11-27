pub fn minimum_average_difference(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let mut prefix: i64 = 0;
    let mut best_diff: i64 = -1;
    let mut best_index: i64 = 0;

    i = 0;
    while i < n {
        prefix += nums[i];

        let left_count: i64 = (i as i64) + 1;
        let left_avg: i64 = prefix / left_count;

        let right_count_usize: usize = n - i - 1;
        let right_avg: i64;
        if right_count_usize == 0 {
            right_avg = 0;
        } else {
            right_avg = (total - prefix) / (right_count_usize as i64);
        }

        let diff: i64;
        if left_avg >= right_avg {
            diff = left_avg - right_avg;
        } else {
            diff = right_avg - left_avg;
        }

        if best_diff < 0 || diff < best_diff {
            best_diff = diff;
            best_index = i as i64;
        }

        i += 1;
    }

    best_index
}
