pub fn total_hamming_distance(nums: &[i64]) -> i64 {
    let n: i64 = nums.len() as i64;
    let mut total: i64 = 0;
    let mut bit: usize = 0;

    while bit < 32 {
        let mask: i64 = 1_i64 << bit;
        let mut ones: i64 = 0;
        let mut i: usize = 0;

        while i < nums.len() {
            if (nums[i] & mask) != 0 {
                ones += 1;
            }
            i += 1;
        }

        total += ones * (n - ones);
        bit += 1;
    }

    total
}
