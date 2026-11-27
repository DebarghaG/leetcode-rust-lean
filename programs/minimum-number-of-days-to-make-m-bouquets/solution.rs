fn can_make(bloom_day: &[i64], m: i64, k: i64, day: i64) -> bool {
    let mut bouquets: i64 = 0;
    let mut flowers: i64 = 0;
    let mut i: usize = 0;

    while i < bloom_day.len() {
        if bloom_day[i] <= day {
            flowers = flowers + 1;
            if flowers == k {
                bouquets = bouquets + 1;
                flowers = 0;
                if bouquets >= m {
                    return true;
                }
            }
        } else {
            flowers = 0;
        }
        i = i + 1;
    }

    bouquets >= m
}

pub fn min_days(bloomDay: &[i64], m: i64, k: i64) -> i64 {
    if m == 0 {
        return 0;
    }
    if k <= 0 {
        return -1;
    }

    let n: i64 = bloomDay.len() as i64;
    if m * k > n {
        return -1;
    }

    let mut max_day: i64 = 0;
    let mut i: usize = 0;
    while i < bloomDay.len() {
        if bloomDay[i] > max_day {
            max_day = bloomDay[i];
        }
        i = i + 1;
    }

    let mut lo: i64 = 1;
    let mut hi: i64 = max_day;
    let mut ans: i64 = -1;

    while lo <= hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if can_make(bloomDay, m, k, mid) {
            ans = mid;
            hi = mid - 1;
        } else {
            lo = mid + 1;
        }
    }

    ans
}
