pub fn subset_xor_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut bit_or: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        bit_or |= nums[i];
        i += 1;
    }

    let mut multiplier: i64 = 1;
    let mut j: usize = 1;
    while j < n {
        multiplier *= 2;
        j += 1;
    }

    bit_or * multiplier
}
