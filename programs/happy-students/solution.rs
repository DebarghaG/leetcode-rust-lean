pub fn count_ways(nums: &[i64]) -> i64 {
    let n_usize = nums.len();
    let n = n_usize as i64;

    let mut freq: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t <= n_usize {
        freq.push(0);
        t += 1;
    }

    let mut i: usize = 0;
    while i < n_usize {
        let v = nums[i];
        if v >= 0 && v <= n {
            freq[v as usize] += 1;
        }
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut less: i64 = 0;
    let mut k: usize = 0;

    while k <= n_usize {
        if less == k as i64 && freq[k] == 0 {
            ans += 1;
        }
        less += freq[k];
        k += 1;
    }

    ans
}
