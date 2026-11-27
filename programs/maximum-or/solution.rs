pub fn maximum_or(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut factor: i64 = 1;
    let mut t: i64 = 0;
    while t < k {
        factor = factor * 2;
        t += 1;
    }

    let mut suffix: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= n {
        suffix.push(0);
        z += 1;
    }

    let mut i: usize = n;
    while i > 0 {
        i -= 1;
        suffix[i] = suffix[i + 1] | nums[i];
    }

    let mut ans: i64 = 0;
    let mut prefix: i64 = 0;
    let mut j: usize = 0;

    while j < n {
        let shifted = nums[j] * factor;
        let candidate = prefix | shifted | suffix[j + 1];
        if candidate > ans {
            ans = candidate;
        }
        prefix = prefix | nums[j];
        j += 1;
    }

    ans
}
