pub fn arithmetic_triplets(nums: &[i64], diff: i64) -> i64 {
    let n = nums.len();
    let mut count: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            if nums[j] - nums[i] == diff {
                let mut k: usize = j + 1;
                while k < n {
                    if nums[k] - nums[j] == diff {
                        count += 1;
                    }
                    k += 1;
                }
            }
            j += 1;
        }
        i += 1;
    }

    count
}
