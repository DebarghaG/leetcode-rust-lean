pub fn max_absolute_sum(nums: &[i64]) -> i64 {
    let mut cur: i64 = 0;
    let mut max_pref: i64 = 0;
    let mut min_pref: i64 = 0;
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        cur = cur + nums[i];

        if cur > max_pref {
            max_pref = cur;
        }

        if cur < min_pref {
            min_pref = cur;
        }

        i += 1;
    }

    max_pref - min_pref
}
