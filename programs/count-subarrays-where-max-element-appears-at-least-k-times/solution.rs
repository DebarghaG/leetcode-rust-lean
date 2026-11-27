pub fn count_subarrays(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut max_val = nums[0];
    let mut i = 1usize;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut positions: Vec<i64> = Vec::new();
    let mut j = 0usize;
    while j < n {
        if nums[j] == max_val {
            positions.push(j as i64);
        }
        j += 1;
    }

    let m = positions.len();
    let kk = k as usize;

    if kk == 0 || m < kk {
        return 0;
    }

    let n_i64 = n as i64;
    let mut ans: i64 = 0;
    let mut start = 0usize;

    while start + kk <= m {
        let mut left_choices: i64;
        if start == 0 {
            left_choices = positions[start] + 1;
        } else {
            left_choices = positions[start] - positions[start - 1];
        }

        let last_pos = positions[start + kk - 1];
        let right_choices = n_i64 - last_pos;

        ans += left_choices * right_choices;
        start += 1;
    }

    ans
}
