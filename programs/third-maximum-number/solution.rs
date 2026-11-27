pub fn third_max(nums: &[i64]) -> i64 {
    let n: usize = nums.len();

    // Find the maximum value.
    let mut first: i64 = nums[0];
    let mut i: usize = 1;
    while i < n {
        let x: i64 = nums[i];
        if x > first {
            first = x;
        }
        i += 1;
    }

    // Find the largest value strictly less than `first`.
    let mut has_second: bool = false;
    let mut second: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let x: i64 = nums[i];
        if x < first {
            if !has_second {
                second = x;
                has_second = true;
            } else if x > second {
                second = x;
            }
        }
        i += 1;
    }

    if !has_second {
        return first;
    }

    // Find the largest value strictly less than `second`.
    let mut has_third: bool = false;
    let mut third: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let x: i64 = nums[i];
        if x < second {
            if !has_third {
                third = x;
                has_third = true;
            } else if x > third {
                third = x;
            }
        }
        i += 1;
    }

    if has_third {
        return third;
    }
    first
}
