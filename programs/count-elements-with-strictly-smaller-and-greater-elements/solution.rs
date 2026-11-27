pub fn count_elements(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut min_val = nums[0];
    let mut max_val = nums[0];

    let mut i = 1;
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

    let mut count: i64 = 0;
    let mut j = 0;
    while j < n {
        let x = nums[j];
        if x > min_val && x < max_val {
            count += 1;
        }
        j += 1;
    }

    count
}
