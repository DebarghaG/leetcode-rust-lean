pub fn min_operations(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut i = 0;
    while i < n {
        if nums[i] < k {
            return -1;
        }
        i += 1;
    }

    let mut count: i64 = 0;
    i = 0;
    while i < n {
        let value = nums[i];
        if value > k {
            let mut seen = false;
            let mut j = 0;
            while j < i {
                if nums[j] == value {
                    seen = true;
                }
                j += 1;
            }
            if !seen {
                count += 1;
            }
        }
        i += 1;
    }

    count
}
