pub fn min_swaps(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut ones: usize = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] == 1 {
            ones += 1;
        }
        i += 1;
    }

    if ones <= 1 {
        return 0;
    }

    let k = ones;

    let mut cur: i64 = 0;
    let mut j: usize = 0;
    while j < k {
        if nums[j] == 1 {
            cur += 1;
        }
        j += 1;
    }

    let mut best: i64 = cur;
    let mut start: usize = 0;

    while start + 1 < n {
        if nums[start] == 1 {
            cur -= 1;
        }

        let mut add_idx = start + k;
        if add_idx >= n {
            add_idx -= n;
        }

        if nums[add_idx] == 1 {
            cur += 1;
        }

        if cur > best {
            best = cur;
        }

        start += 1;
    }

    (ones as i64) - best
}
