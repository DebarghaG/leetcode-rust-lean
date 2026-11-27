pub fn find_closest_number(nums: &[i64]) -> i64 {
    let mut best = nums[0];
    let mut best_dist = if best < 0 { -best } else { best };

    let mut i: usize = 1;
    while i < nums.len() {
        let x = nums[i];
        let d = if x < 0 { -x } else { x };

        if d < best_dist || (d == best_dist && x > best) {
            best = x;
            best_dist = d;
        }

        i += 1;
    }

    best
}
