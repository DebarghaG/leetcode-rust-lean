pub fn get_max_len(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let mut best: i64 = 0;
    let mut pos: i64 = 0;
    let mut neg: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let x: i64 = nums[i];

        if x == 0 {
            pos = 0;
            neg = 0;
        } else if x > 0 {
            pos = pos + 1;
            if neg > 0 {
                neg = neg + 1;
            } else {
                neg = 0;
            }
        } else {
            let new_pos: i64;
            if neg > 0 {
                new_pos = neg + 1;
            } else {
                new_pos = 0;
            }

            let new_neg: i64 = pos + 1;
            pos = new_pos;
            neg = new_neg;
        }

        if pos > best {
            best = pos;
        }

        i += 1;
    }

    best
}
