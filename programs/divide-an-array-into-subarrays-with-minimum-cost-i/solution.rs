pub fn minimum_cost(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best: i64 = nums[0] + nums[1] + nums[2];

    let mut i: usize = 1;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let cost = nums[0] + nums[i] + nums[j];
            if cost < best {
                best = cost;
            }
            j += 1;
        }
        i += 1;
    }

    best
}
