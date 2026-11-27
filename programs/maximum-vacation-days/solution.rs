pub fn max_vacation_days(flights: &[Vec<i64>], days: &[Vec<i64>]) -> i64 {
    let n = days.len();
    if n == 0 {
        return 0;
    }
    let k = days[0].len();
    if k == 0 {
        return 0;
    }

    let neg: i64 = -1_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        if i == 0 {
            dp.push(0);
        } else {
            dp.push(neg);
        }
        i += 1;
    }

    let mut week = 0;
    while week < k {
        let mut next_dp: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            next_dp.push(neg);
            j += 1;
        }

        let mut from = 0;
        while from < n {
            if dp[from] >= 0 {
                let mut to = 0;
                while to < n {
                    if from == to || flights[from][to] == 1 {
                        let candidate = dp[from] + days[to][week];
                        if candidate > next_dp[to] {
                            next_dp[to] = candidate;
                        }
                    }
                    to += 1;
                }
            }
            from += 1;
        }

        dp = next_dp;
        week += 1;
    }

    let mut answer = neg;
    let mut city = 0;
    while city < n {
        if dp[city] > answer {
            answer = dp[city];
        }
        city += 1;
    }

    answer
}
