pub fn make_string_good(s: &[u8]) -> i64 {
    let mut cnt: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        cnt.push(0);
        i += 1;
    }

    let mut p: usize = 0;
    while p < s.len() {
        let pos: usize = (s[p] - b'a') as usize;
        cnt[pos] = cnt[pos] + 1;
        p += 1;
    }

    let mut max_count: i64 = 0;
    i = 0;
    while i < 26 {
        if cnt[i] > max_count {
            max_count = cnt[i];
        }
        i += 1;
    }

    let mut ans: i64 = s.len() as i64;
    let mut target: i64 = 1;

    while target <= max_count {
        let c0 = cnt[0];

        // State choice 0: letter 0 becomes absent.
        let mut dp0 = c0;
        let mut surplus0 = c0;

        // State choice 1: letter 0 has frequency target.
        let mut dp1: i64;
        let mut surplus1: i64;
        if c0 >= target {
            dp1 = c0 - target;
            surplus1 = c0 - target;
        } else {
            dp1 = target - c0;
            surplus1 = 0;
        }

        let mut idx: usize = 1;
        while idx < 26 {
            let c = cnt[idx];

            // Current letter becomes absent.
            let cost0 = c;
            let new_surplus0 = c;

            // Current letter becomes target.
            let cost1: i64;
            let deficit1: i64;
            let new_surplus1: i64;
            if c >= target {
                cost1 = c - target;
                deficit1 = 0;
                new_surplus1 = c - target;
            } else {
                cost1 = target - c;
                deficit1 = target - c;
                new_surplus1 = 0;
            }

            // Current letter becomes absent: no deficit to fill.
            let choose0_from0 = dp0 + cost0;
            let choose0_from1 = dp1 + cost0;
            let ndp0 = if choose0_from0 < choose0_from1 {
                choose0_from0
            } else {
                choose0_from1
            };

            // Current letter becomes target: can receive surplus from previous letter.
            let save0 = if surplus0 < deficit1 {
                surplus0
            } else {
                deficit1
            };
            let save1 = if surplus1 < deficit1 {
                surplus1
            } else {
                deficit1
            };

            let choose1_from0 = dp0 + cost1 - save0;
            let choose1_from1 = dp1 + cost1 - save1;
            let ndp1 = if choose1_from0 < choose1_from1 {
                choose1_from0
            } else {
                choose1_from1
            };

            dp0 = ndp0;
            dp1 = ndp1;
            surplus0 = new_surplus0;
            surplus1 = new_surplus1;

            idx += 1;
        }

        let current_best = if dp0 < dp1 { dp0 } else { dp1 };
        if current_best < ans {
            ans = current_best;
        }

        target += 1;
    }

    ans
}
