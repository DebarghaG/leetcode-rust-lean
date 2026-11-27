pub fn min_length_after_removals(nums: &[i64]) -> i64 {
    let n_usize = nums.len();
    if n_usize == 0 {
        return 0;
    }

    let n = n_usize as i64;
    let mut max_freq: i64 = 0;
    let mut i: usize = 0;

    while i < n_usize {
        let value = nums[i];
        let mut j: usize = i + 1;
        while j < n_usize && nums[j] == value {
            j += 1;
        }

        let freq = (j - i) as i64;
        if freq > max_freq {
            max_freq = freq;
        }

        i = j;
    }

    if max_freq > n - max_freq {
        return max_freq - (n - max_freq);
    }

    if n % 2 == 0 {
        0
    } else {
        1
    }
}
