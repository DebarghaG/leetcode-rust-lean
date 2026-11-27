pub fn minimum_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best: i64 = 1_000_000_000;

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let mut k: usize = j + 1;
            while k < n {
                if nums[i] < nums[j] && nums[k] < nums[j] {
                    let sum = nums[i] + nums[j] + nums[k];
                    if sum < best {
                        best = sum;
                    }
                }
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }

    if best == 1_000_000_000 {
        -1
    } else {
        best
    }
}
