pub fn max_dist_to_closest(seats: &[i64]) -> i64 {
    let n: usize = seats.len();
    let mut ans: i64 = 0;
    let mut last: i64 = -1;

    for i in 0..n {
        if seats[i] == 1 {
            let idx: i64 = i as i64;
            if last == -1 {
                if idx > ans {
                    ans = idx;
                }
            } else {
                let d: i64 = (idx - last) / 2;
                if d > ans {
                    ans = d;
                }
            }
            last = idx;
        }
    }

    if last != -1 {
        let trailing: i64 = (n as i64) - 1 - last;
        if trailing > ans {
            ans = trailing;
        }
    }

    ans
}
