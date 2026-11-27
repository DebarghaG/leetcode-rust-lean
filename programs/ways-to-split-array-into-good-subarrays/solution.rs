pub fn number_of_good_subarray_splits(nums: &[i64]) -> i64 {
    let n = nums.len();
    let modulus: i64 = 1000000007;

    // First pass: collect the positions of the 1s.
    let mut positions: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if nums[i] == 1 {
            positions.push(i as i64);
        }
        i += 1;
    }

    let count = positions.len();
    // No 1s at all -> impossible to split into good subarrays.
    if count == 0 {
        return 0;
    }

    // Second pass: pure accumulate the product of gaps between consecutive 1s.
    let mut answer: i64 = 1;
    let mut j: usize = 1;
    while j < count {
        let gap: i64 = positions[j] - positions[j - 1];
        answer = (answer * gap) % modulus;
        j += 1;
    }

    answer
}
