pub fn min_refuel_stops(target: i64, start_fuel: i64, stations: &[Vec<i64>]) -> i64 {
    let n = stations.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i <= n {
        if i == 0 {
            dp.push(start_fuel);
        } else {
            dp.push(0);
        }
        i = i + 1;
    }

    let mut s = 0;
    while s < n {
        let pos = stations[s][0];
        let fuel = stations[s][1];

        let mut k = s + 1;
        while k > 0 {
            k = k - 1;
            if dp[k] >= pos {
                let cand = dp[k] + fuel;
                if cand > dp[k + 1] {
                    dp[k + 1] = cand;
                }
            }
        }

        s = s + 1;
    }

    let mut j = 0;
    while j <= n {
        if dp[j] >= target {
            return j as i64;
        }
        j = j + 1;
    }

    -1
}
