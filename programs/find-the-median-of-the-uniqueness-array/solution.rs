pub fn median_of_uniqueness_array(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // Find the maximum value to size the frequency array.
    let mut max_val: usize = 0;
    let mut i = 0;
    while i < n {
        let v = nums[i] as usize;
        if v > max_val {
            max_val = v;
        }
        i += 1;
    }

    let n_i64 = n as i64;
    let total: i64 = n_i64 * (n_i64 + 1) / 2;
    // Index of the lower median in 0-based indexing.
    let k: i64 = (total - 1) / 2;
    // We need the smallest x such that count of subarrays with distinct <= x is at least target.
    let target: i64 = k + 1;

    let mut lo: i64 = 1;
    let mut hi: i64 = n_i64;

    while lo < hi {
        let mid = (lo + hi) / 2;
        let cnt = count_leq(nums, mid, max_val);
        if cnt >= target {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

fn count_leq(nums: &[i64], x: i64, max_val: usize) -> i64 {
    let n = nums.len();

    // Frequency array. Size is max_val + 1, built manually.
    let mut freq: Vec<i64> = Vec::new();
    let mut i = 0;
    while i <= max_val {
        freq.push(0);
        i += 1;
    }

    let mut left: usize = 0;
    let mut distinct: i64 = 0;
    let mut total: i64 = 0;
    let mut right: usize = 0;

    while right < n {
        let v = nums[right] as usize;
        if freq[v] == 0 {
            distinct += 1;
        }
        freq[v] += 1;

        while distinct > x {
            let u = nums[left] as usize;
            freq[u] -= 1;
            if freq[u] == 0 {
                distinct -= 1;
            }
            left += 1;
        }

        total += (right - left + 1) as i64;
        right += 1;
    }

    total
}
