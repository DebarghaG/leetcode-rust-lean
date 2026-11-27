pub fn can_choose(groups: &[Vec<i64>], nums: &[i64]) -> bool {
    let m = nums.len();
    let mut pos: usize = 0;
    let mut g: usize = 0;

    while g < groups.len() {
        let glen = groups[g].len();
        let mut found = false;
        let mut start = pos;

        while start + glen <= m && !found {
            let mut k: usize = 0;
            let mut ok = true;

            while k < glen && ok {
                if nums[start + k] != groups[g][k] {
                    ok = false;
                } else {
                    k += 1;
                }
            }

            if ok {
                found = true;
                pos = start + glen;
            } else {
                start += 1;
            }
        }

        if !found {
            return false;
        }

        g += 1;
    }

    true
}
