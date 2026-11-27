pub fn min_bitwise_array(nums: &[i64]) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < nums.len() {
        let n = nums[i];

        if n % 2 == 0 {
            result.push(-1);
        } else {
            let mut p: i64 = 1;

            while (n / p) % 2 == 1 {
                p = p * 2;
            }

            let value = n - p / 2;
            result.push(value);
        }

        i = i + 1;
    }

    result
}
