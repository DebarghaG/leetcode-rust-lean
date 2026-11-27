pub fn count_pairs(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;

    for i in 0..n {
        for j in (i + 1)..n {
            if nums[i] == nums[j] {
                let product = (i as i64) * (j as i64);
                if product % k == 0 {
                    ans += 1;
                }
            }
        }
    }

    ans
}
