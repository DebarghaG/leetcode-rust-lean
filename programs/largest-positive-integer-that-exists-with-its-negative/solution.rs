pub fn find_max_k(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        let v = nums[i];
        if v > 0 && v > best {
            let target = -v;
            let mut found = false;
            let mut j: usize = 0;

            while j < n {
                if nums[j] == target {
                    found = true;
                }
                j += 1;
            }

            if found {
                best = v;
            }
        }

        i += 1;
    }

    best
}
