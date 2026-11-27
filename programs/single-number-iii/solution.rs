pub fn single_number(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut xor_sum: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        xor_sum = xor_sum ^ nums[i];
        i += 1;
    }

    let mask: i64 = xor_sum & (-xor_sum);

    let mut first: i64 = 0;
    let mut second: i64 = 0;

    let mut j: usize = 0;
    while j < n {
        let value = nums[j];
        if (value & mask) != 0 {
            first = first ^ value;
        } else {
            second = second ^ value;
        }
        j += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(first);
    result.push(second);
    result
}
