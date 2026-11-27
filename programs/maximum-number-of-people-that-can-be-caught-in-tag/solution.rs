pub fn catch_maximum_amountof_people(team: &[i64], dist: i64) -> i64 {
    let n = team.len();
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut ans: i64 = 0;

    while i < n && j < n {
        while i < n && team[i] != 0 {
            i += 1;
        }
        while j < n && team[j] != 1 {
            j += 1;
        }

        if i < n && j < n {
            let diff: i64 = if i > j {
                (i - j) as i64
            } else {
                (j - i) as i64
            };

            if diff <= dist {
                ans += 1;
                i += 1;
                j += 1;
            } else if i < j {
                i += 1;
            } else {
                j += 1;
            }
        }
    }

    ans
}
