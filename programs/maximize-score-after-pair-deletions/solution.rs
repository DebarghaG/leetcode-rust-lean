pub fn max_score(nums: &[i64]) -> i64 {
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

    if n % 2 == 1 {
        let mut min_val = nums[0];
        let mut j: usize = 1;
        while j < n {
            if nums[j] < min_val {
                min_val = nums[j];
            }
            j += 1;
        }
        total - min_val
    } else {
        let mut min_pair = nums[0] + nums[1];
        let mut k: usize = 1;
        while k + 1 < n {
            let s = nums[k] + nums[k + 1];
            if s < min_pair {
                min_pair = s;
            }
            k += 1;
        }
        total - min_pair
    }
}
