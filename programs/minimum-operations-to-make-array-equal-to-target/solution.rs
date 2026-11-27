pub fn minimum_operations(nums: &[i64], target: &[i64]) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;

    let mut prev_pos: i64 = 0;
    let mut prev_neg: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let d = target[i] - nums[i];

        let pos = if d > 0 { d } else { 0 };
        let neg = if d < 0 { -d } else { 0 };

        if pos > prev_pos {
            ans += pos - prev_pos;
        }
        if neg > prev_neg {
            ans += neg - prev_neg;
        }

        prev_pos = pos;
        prev_neg = neg;

        i += 1;
    }

    ans
}
