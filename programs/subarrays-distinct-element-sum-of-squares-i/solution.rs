pub fn sum_counts(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i;
        let mut distinct: i64 = 0;

        while j < n {
            let mut seen_before: bool = false;
            let mut k: usize = i;

            while k < j {
                if nums[k] == nums[j] {
                    seen_before = true;
                }
                k += 1;
            }

            if !seen_before {
                distinct += 1;
            }

            total += distinct * distinct;
            j += 1;
        }

        i += 1;
    }

    total
}
