pub fn is_consecutive(nums: &[i64]) -> bool {
    let n = nums.len();
    if n == 0 {
        return true;
    }

    let mut min: i64 = nums[0];
    let mut max: i64 = nums[0];

    let mut i: usize = 1;
    while i < n {
        let v = nums[i];
        if v < min {
            min = v;
        }
        if v > max {
            max = v;
        }
        i += 1;
    }

    let span: i64 = max - min + 1;
    if span != n as i64 {
        return false;
    }

    let mut seen: Vec<i64> = Vec::new();
    let mut k: i64 = 0;
    while k < span {
        seen.push(0);
        k += 1;
    }

    let mut j: usize = 0;
    while j < n {
        let idx_i: i64 = nums[j] - min;
        let idx: usize = idx_i as usize;

        if seen[idx] != 0 {
            return false;
        }
        seen[idx] = 1;

        j += 1;
    }

    true
}
