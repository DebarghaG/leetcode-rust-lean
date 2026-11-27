pub fn subsequence_sum_or(nums: &[i64]) -> i64 {
    let mut ans: i64 = 0;
    let mut sum: i64 = 0;
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];

        ans = ans | x;

        sum = sum + x;
        ans = ans | sum;

        i = i + 1;
    }

    ans
}
