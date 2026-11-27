pub fn smallest_range_i(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut mn = nums[0];
    let mut mx = nums[0];
    let mut i: usize = 1;

    while i < n {
        let v = nums[i];
        if v < mn {
            mn = v;
        }
        if v > mx {
            mx = v;
        }
        i += 1;
    }

    let d = mx - mn - 2 * k;
    if d > 0 {
        d
    } else {
        0
    }
}
