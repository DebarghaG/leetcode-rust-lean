pub fn incremovable_subarray_count(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut p: usize = 1;
    while p < n && nums[p - 1] < nums[p] {
        p += 1;
    }

    let n_i = n as i64;

    if p == n {
        return n_i * (n_i + 1) / 2;
    }

    let mut s: usize = n - 1;
    while s > 0 && nums[s - 1] < nums[s] {
        s -= 1;
    }

    let mut ans: i64 = 0;

    let mut b: usize = s;
    if b == 0 {
        b = 1;
    }
    ans = ans + (n_i - (b as i64) + 1);

    let mut a: usize = 1;
    while a <= p {
        let min_b = a + 1;
        if b < min_b {
            b = min_b;
        }
        if b < s {
            b = s;
        }

        while b < n && nums[b] <= nums[a - 1] {
            b += 1;
        }

        ans = ans + (n_i - (b as i64) + 1);
        a += 1;
    }

    ans
}
