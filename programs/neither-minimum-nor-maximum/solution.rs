pub fn find_non_min_or_max(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return -1;
    }

    let mut min_val = nums[0];
    let mut max_val = nums[0];

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];
        if x < min_val {
            min_val = x;
        }
        if x > max_val {
            max_val = x;
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < n {
        let x = nums[j];
        if x != min_val && x != max_val {
            return x;
        }
        j += 1;
    }

    -1
}
