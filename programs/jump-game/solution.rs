pub fn can_jump(nums: &[i64]) -> bool {
    let n = nums.len();
    let mut result: bool = true;

    if n > 1 {
        let mut i: usize = 0;
        let mut max_reach: i64 = 0;
        let mut ok: bool = true;

        while i < n {
            let pos: i64 = i as i64;

            if pos > max_reach {
                ok = false;
            } else {
                let next_reach = pos + nums[i];
                if next_reach > max_reach {
                    max_reach = next_reach;
                }
            }

            i += 1;
        }

        result = ok;
    }

    result
}
