pub fn sum_indices_with_k_set_bits(nums: &[i64], k: i64) -> i64 {
    let mut sum: i64 = 0;
    let n: usize = nums.len();

    let mut i: usize = 0;
    while i < n {
        let mut x: usize = i;
        let mut count: i64 = 0;

        while x > 0 {
            if x % 2 == 1 {
                count += 1;
            }
            x = x / 2;
        }

        if count == k {
            sum += nums[i];
        }

        i += 1;
    }

    sum
}
