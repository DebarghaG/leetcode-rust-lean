pub fn is_zero_array(nums: &[i64], queries: &[Vec<i64>]) -> bool {
    let n = nums.len();

    let mut diff: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n + 1 {
        diff.push(0);
        i += 1;
    }

    let mut q = 0usize;
    while q < queries.len() {
        let l = queries[q][0] as usize;
        let r = queries[q][1] as usize;

        diff[l] += 1;
        diff[r + 1] -= 1;

        q += 1;
    }

    let mut coverage: i64 = 0;
    i = 0usize;
    while i < n {
        coverage += diff[i];
        if coverage < nums[i] {
            return false;
        }
        i += 1;
    }

    true
}
