pub fn sub_array_ranges(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut min_val: i64 = nums[i];
        let mut max_val: i64 = nums[i];
        let mut j: usize = i;

        while j < n {
            let x: i64 = nums[j];

            if x < min_val {
                min_val = x;
            }
            if x > max_val {
                max_val = x;
            }

            total += max_val - min_val;
            j += 1;
        }

        i += 1;
    }

    total
}
