pub fn maximum_strong_pair_xor(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best = 0i64;
    let mut i = 0usize;

    while i < n {
        let mut j = i;
        while j < n {
            let x = nums[i];
            let y = nums[j];

            let diff = if x >= y { x - y } else { y - x };
            let min_val = if x <= y { x } else { y };

            if diff <= min_val {
                let value = x ^ y;
                if value > best {
                    best = value;
                }
            }

            j += 1;
        }
        i += 1;
    }

    best
}
