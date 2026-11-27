pub fn min_operations(nums: &[i64]) -> i64 {
    let mut total_increments: i64 = 0;
    let mut max_doublings: i64 = 0;

    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let mut x = nums[i];
        let mut bit_count: i64 = 0;
        let mut bit_length: i64 = 0;

        while x > 0 {
            if x % 2 == 1 {
                bit_count += 1;
            }
            x = x / 2;
            bit_length += 1;
        }

        total_increments += bit_count;

        if bit_length > 0 {
            let doublings = bit_length - 1;
            if doublings > max_doublings {
                max_doublings = doublings;
            }
        }

        i += 1;
    }

    total_increments + max_doublings
}
