pub fn maximum_triplet_value(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let mut k: usize = j + 1;
            while k < n {
                let value = (nums[i] - nums[j]) * nums[k];
                if value > best {
                    best = value;
                }
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }

    best
}
