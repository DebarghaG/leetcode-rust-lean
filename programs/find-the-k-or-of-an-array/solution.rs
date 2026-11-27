pub fn find_k_or(nums: &[i64], k: i64) -> i64 {
    let mut ans: i64 = 0;
    let mut bit: usize = 0;

    while bit < 32 {
        let mut count: i64 = 0;
        let mut i: usize = 0;

        while i < nums.len() {
            if ((nums[i] >> bit) & 1) == 1 {
                count += 1;
            }
            i += 1;
        }

        if count >= k {
            ans = ans | (1i64 << bit);
        }

        bit += 1;
    }

    ans
}
