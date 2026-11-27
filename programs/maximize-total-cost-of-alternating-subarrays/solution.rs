pub fn maximum_total_cost(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut pos: i64 = nums[0];
    let mut neg: i64 = -1000000000000000000;

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];
        let best = if pos > neg { pos } else { neg };

        let new_pos = best + x;
        let new_neg = pos - x;

        pos = new_pos;
        neg = new_neg;
        i += 1;
    }

    if pos > neg { pos } else { neg }
}
