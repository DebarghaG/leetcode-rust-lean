pub fn maximum_alternating_subarray_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut plus: i64 = nums[0];
    let mut minus: i64 = 0;
    let mut best: i64 = nums[0];

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];

        let extend_plus = minus + x;
        let new_plus = if extend_plus > x { extend_plus } else { x };
        let new_minus = plus - x;

        if new_plus > best {
            best = new_plus;
        }
        if new_minus > best {
            best = new_minus;
        }

        plus = new_plus;
        minus = new_minus;
        i = i + 1;
    }

    best
}
