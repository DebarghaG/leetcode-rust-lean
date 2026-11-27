pub fn can_partition(nums: &[i64]) -> bool {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    if total % 2 != 0 {
        return false;
    }

    let target_i64 = total / 2;
    let target = target_i64 as usize;

    let mut dp: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j <= target {
        dp.push(false);
        j += 1;
    }

    dp[0] = true;

    let mut idx: usize = 0;
    while idx < n {
        let value = nums[idx];

        if value <= target_i64 {
            let value_usize = value as usize;
            let mut s = target;

            while s >= value_usize {
                if dp[s - value_usize] {
                    dp[s] = true;
                }

                if s == 0 {
                    break;
                }
                s -= 1;
            }
        }

        idx += 1;
    }

    dp[target]
}
