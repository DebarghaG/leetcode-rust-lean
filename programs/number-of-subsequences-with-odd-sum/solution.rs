pub fn subsequence_count(nums: &[i64]) -> i64 {
    let mut i: usize = 0;
    let mut n: i64 = 0;
    let mut has_odd: bool = false;

    while i < nums.len() {
        if nums[i] % 2 != 0 {
            has_odd = true;
        }
        n += 1;
        i += 1;
    }

    if !has_odd {
        return 0;
    }

    let mut exp: i64 = n - 1;
    let mut res: i64 = 1;
    let modulus: i64 = 1000000007;

    while exp > 0 {
        res = (res * 2) % modulus;
        exp -= 1;
    }

    res
}
