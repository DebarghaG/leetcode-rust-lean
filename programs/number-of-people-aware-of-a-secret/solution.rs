pub fn people_aware_of_secret(n: i64, delay: i64, forget: i64) -> i64 {
    const MOD: i64 = 1000000007;

    let n_usize = n as usize;

    let mut new_people: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n_usize + 1 {
        new_people.push(0);
        i += 1;
    }

    if n_usize >= 1 {
        new_people[1] = 1;
    }

    let mut day: usize = 2;
    while day <= n_usize {
        let day_i = day as i64;

        let mut start = day_i - forget + 1;
        if start < 1 {
            start = 1;
        }

        let end = day_i - delay;

        let mut total: i64 = 0;
        let mut d = start;
        while d <= end {
            total += new_people[d as usize];
            if total >= MOD {
                total -= MOD;
            }
            d += 1;
        }

        new_people[day] = total;
        day += 1;
    }

    let mut start_ret = n - forget + 1;
    if start_ret < 1 {
        start_ret = 1;
    }

    let mut ans: i64 = 0;
    let mut d = start_ret;
    while d <= n {
        ans += new_people[d as usize];
        if ans >= MOD {
            ans -= MOD;
        }
        d += 1;
    }

    ans
}
