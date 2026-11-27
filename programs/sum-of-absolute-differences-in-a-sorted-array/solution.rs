pub fn get_sum_absolute_differences(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut n_i64: i64 = 0;
    let mut k: usize = 0;
    while k < n {
        total = total + nums[k];
        n_i64 = n_i64 + 1;
        k = k + 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut prefix: i64 = 0;
    let mut i: usize = 0;
    let mut left_count: i64 = 0;

    while i < n {
        let x = nums[i];
        let left_sum = prefix;
        let right_sum = total - prefix - x;
        let right_count = n_i64 - left_count - 1;

        let value = x * left_count - left_sum + right_sum - x * right_count;
        result.push(value);

        prefix = prefix + x;
        i = i + 1;
        left_count = left_count + 1;
    }

    result
}
