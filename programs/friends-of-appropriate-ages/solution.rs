pub fn num_friend_requests(ages: &[i64]) -> i64 {
    let mut cnt: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 121 {
        cnt.push(0);
        i += 1;
    }

    let n = ages.len();
    let mut p: usize = 0;
    while p < n {
        let a = ages[p];

        let mut idx: usize = 1;
        let mut age_val: i64 = 1;
        while age_val <= 120 {
            if a == age_val {
                cnt[idx] = cnt[idx] + 1;
            }
            idx += 1;
            age_val += 1;
        }

        p += 1;
    }

    let mut ans: i64 = 0;

    let mut xi: usize = 1;
    let mut x: i64 = 1;
    while x <= 120 {
        let cx = cnt[xi];
        if cx > 0 {
            let mut yi: usize = 1;
            let mut y: i64 = 1;
            while y <= 120 {
                let cy = cnt[yi];
                if cy > 0 {
                    if y <= x && 2 * y > x + 14 && !(y > 100 && x < 100) {
                        let mut add = cx * cy;
                        if x == y {
                            add = add - cx;
                        }
                        ans = ans + add;
                    }
                }
                yi += 1;
                y += 1;
            }
        }
        xi += 1;
        x += 1;
    }

    ans
}
