pub fn check_array(nums: &[i64], k: i64) -> bool {
    if k <= 0 {
        return false;
    }

    let n = nums.len();
    let k_usize = k as usize;

    let mut diff: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i <= n {
        diff.push(0);
        i += 1;
    }

    let mut current: i64 = 0;
    let mut idx = 0usize;

    while idx < n {
        current = current + diff[idx];
        let value = nums[idx];

        if current > value {
            return false;
        }

        let need = value - current;
        if need > 0 {
            if idx + k_usize > n {
                return false;
            }

            current = current + need;
            let remove_at = idx + k_usize;
            diff[remove_at] = diff[remove_at] - need;
        }

        idx += 1;
    }

    true
}
