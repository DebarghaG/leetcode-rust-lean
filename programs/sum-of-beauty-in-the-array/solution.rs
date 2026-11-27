pub fn sum_of_beauties(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }

    let mut suffix_min: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        suffix_min.push(0);
        i += 1;
    }

    let mut idx = n;
    let mut cur_min = nums[n - 1];
    while idx > 0 {
        idx -= 1;
        if nums[idx] < cur_min {
            cur_min = nums[idx];
        }
        suffix_min[idx] = cur_min;
    }

    let mut total = 0i64;
    let mut prefix_max = nums[0];
    let mut i = 1;

    while i + 1 < n {
        if prefix_max < nums[i] && nums[i] < suffix_min[i + 1] {
            total += 2;
        } else if nums[i - 1] < nums[i] && nums[i] < nums[i + 1] {
            total += 1;
        }

        if nums[i] > prefix_max {
            prefix_max = nums[i];
        }

        i += 1;
    }

    total
}
