pub fn minimum_operations(nums: &[i64]) -> i64 {
    let mut count: i64 = 0;
    let n = nums.len();

    let mut i: usize = 0;
    while i < n {
        let v = nums[i];
        if v > 0 {
            let mut seen: bool = false;
            let mut j: usize = 0;
            while j < i {
                if nums[j] == v {
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
