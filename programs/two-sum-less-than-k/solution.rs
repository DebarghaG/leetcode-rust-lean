pub fn two_sum_less_than_k(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut best: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;

        while j < n {
            let sum = nums[i] + nums[j];

            if sum < k && sum > best {
                best = sum;
            }

            j += 1;
        }

        i += 1;
    }

    best
}
