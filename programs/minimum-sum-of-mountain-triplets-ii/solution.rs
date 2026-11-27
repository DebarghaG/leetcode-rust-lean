pub fn minimum_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return -1;
    }

    let mut suffix_min: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        suffix_min.push(0);
        i += 1;
    }

    let mut current_min: i64 = nums[n - 1];
    let mut idx: usize = n;
    while idx > 0 {
        idx -= 1;
        if nums[idx] < current_min {
            current_min = nums[idx];
        }
        suffix_min[idx] = current_min;
    }

    let mut ans: i64 = -1;
    let mut left_min: i64 = nums[0];
    let mut j: usize = 1;

    while j + 1 < n {
        if left_min < nums[j] && suffix_min[j + 1] < nums[j] {
            let sum = left_min + nums[j] + suffix_min[j + 1];
            if ans == -1 || sum < ans {
                ans = sum;
            }
        }

        if nums[j] < left_min {
            left_min = nums[j];
        }

        j += 1;
    }

    ans
}
