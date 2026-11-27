pub fn min_bitwise_array(nums: &[i64]) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < nums.len() {
        let n = nums[i];

        if n % 2 == 0 {
            // Only even prime is 2, which has no valid answer.
            ans.push(-1);
        } else {
            // n is odd: bit 0 is set, so at least one trailing 1 exists.
            // cleared = n & (n + 1) removes all trailing 1 bits.
            // r = value of the trailing-ones run = n - cleared.
            // The smallest answer is n - 2^(cnt-1) where cnt is the run length,
            // and 2^(cnt-1) == (r + 1) / 2.
            let cleared = n & (n + 1);
            let r = n - cleared;
            let p = (r + 1) / 2;
            ans.push(n - p);
        }

        i += 1;
    }

    ans
}
