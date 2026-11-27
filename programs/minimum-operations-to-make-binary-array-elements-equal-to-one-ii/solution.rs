pub fn min_operations(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let mut ops: i64 = 0;
    let mut state: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let cur: i64 = nums[i];
        let mut eff: i64 = cur;
        if state == 1 {
            eff = 1 - cur;
        }
        if eff == 0 {
            ops = ops + 1;
            if state == 1 {
                state = 0;
            } else {
                state = 1;
            }
        }
        i = i + 1;
    }

    ops
}
