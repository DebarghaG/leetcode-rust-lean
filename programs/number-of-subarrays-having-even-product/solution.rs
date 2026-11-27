pub fn even_product(nums: &[i64]) -> i64 {
    let n = nums.len();
    let n_i = n as i64;
    let total = n_i * (n_i + 1) / 2;

    let mut odd_subarrays: i64 = 0;
    let mut odd_run: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if nums[i] % 2 == 0 {
            odd_subarrays = odd_subarrays + odd_run * (odd_run + 1) / 2;
            odd_run = 0;
        } else {
            odd_run = odd_run + 1;
        }
        i = i + 1;
    }

    odd_subarrays = odd_subarrays + odd_run * (odd_run + 1) / 2;

    total - odd_subarrays
}
