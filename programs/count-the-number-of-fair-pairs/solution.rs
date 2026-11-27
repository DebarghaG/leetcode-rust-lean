pub fn count_fair_pairs(nums: &[i64], lower: i64, upper: i64) -> i64 {
    let n = nums.len();
    let mut sorted: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }

    sorted.sort();

    let m = sorted.len();
    if m == 0 {
        return 0;
    }

    let mut count_upper: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = m - 1;

    while left < right {
        if sorted[left] + sorted[right] <= upper {
            count_upper += (right - left) as i64;
            left += 1;
        } else {
            right -= 1;
        }
    }

    let mut count_below_lower: i64 = 0;
    let mut left2: usize = 0;
    let mut right2: usize = m - 1;

    while left2 < right2 {
        if sorted[left2] + sorted[right2] < lower {
            count_below_lower += (right2 - left2) as i64;
            left2 += 1;
        } else {
            right2 -= 1;
        }
    }

    count_upper - count_below_lower
}
