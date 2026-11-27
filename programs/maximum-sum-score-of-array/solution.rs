pub fn maximum_sum_score(nums: &[i64]) -> i64 {
    let n: usize = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let mut ans: i64 = nums[0];
    let mut prefix_before: i64 = 0;

    i = 0;
    while i < n {
        let prefix_including = prefix_before + nums[i];
        let suffix_sum = total - prefix_before;
        let score = if prefix_including > suffix_sum {
            prefix_including
        } else {
            suffix_sum
        };

        if score > ans {
            ans = score;
        }

        prefix_before = prefix_including;
        i += 1;
    }

    ans
}
