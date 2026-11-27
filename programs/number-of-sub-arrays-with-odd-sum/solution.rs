pub fn num_of_subarrays(arr: &[i64]) -> i64 {
    const MOD: i64 = 1_000_000_007;

    let n = arr.len();
    let mut even_prefix: i64 = 1;
    let mut odd_prefix: i64 = 0;
    let mut parity: i64 = 0;
    let mut ans: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let x = arr[i];
        if x % 2 != 0 {
            parity = 1 - parity;
        }

        if parity == 0 {
            ans = (ans + odd_prefix) % MOD;
            even_prefix += 1;
        } else {
            ans = (ans + even_prefix) % MOD;
            odd_prefix += 1;
        }

        i += 1;
    }

    ans
}
