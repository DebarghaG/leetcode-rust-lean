pub fn find_k_distant_indices(nums: &[i64], key: i64, k: i64) -> Vec<i64> {
    let n = nums.len();
    let mut result: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        let mut found: bool = false;

        while j < n {
            if nums[j] == key {
                let diff: usize = if i >= j { i - j } else { j - i };
                if (diff as i64) <= k {
                    found = true;
                }
            }
            j += 1;
        }

        if found {
            result.push(i as i64);
        }

        i += 1;
    }

    result
}
