pub fn find_pairs(nums: &[i64], k: i64) -> i64 {
    if k < 0 {
        return 0;
    }

    let n = nums.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut is_first: bool = true;
        let mut j: usize = 0;
        while j < i {
            if nums[j] == nums[i] {
                is_first = false;
            }
            j += 1;
        }

        if is_first {
            if k == 0 {
                let mut freq: i64 = 0;
                let mut t: usize = 0;
                while t < n {
                    if nums[t] == nums[i] {
                        freq += 1;
                    }
                    t += 1;
                }
                if freq >= 2 {
                    count += 1;
                }
            } else {
                let target: i64 = nums[i] + k;
                let mut found: bool = false;
                let mut t: usize = 0;
                while t < n {
                    if nums[t] == target {
                        found = true;
                    }
                    t += 1;
                }
                if found {
                    count += 1;
                }
            }
        }

        i += 1;
    }

    count
}
