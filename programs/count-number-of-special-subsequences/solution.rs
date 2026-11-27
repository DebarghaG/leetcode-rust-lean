pub fn count_special_subsequences(nums: &[i64]) -> i64 {
    const MOD: i64 = 1_000_000_007;

    let mut dp0: i64 = 0;
    let mut dp1: i64 = 0;
    let mut dp2: i64 = 0;

    let mut i: usize = 0;
    while i < nums.len() {
        let x = nums[i];
        if x == 0 {
            dp0 = (2 * dp0 + 1) % MOD;
        } else if x == 1 {
            dp1 = (2 * dp1 + dp0) % MOD;
        } else {
            dp2 = (2 * dp2 + dp1) % MOD;
        }
        i += 1;
    }

    dp2
}
