pub fn maximum_candies(candies: &[i64], k: i64) -> i64 {
    let n = candies.len();
    if n == 0 || k <= 0 {
        return 0;
    }

    let mut max_candy: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if candies[i] > max_candy {
            max_candy = candies[i];
        }
        i += 1;
    }

    let mut low: i64 = 0;
    let mut high: i64 = max_candy + 1;

    while low + 1 < high {
        let mid: i64 = low + (high - low) / 2;

        let mut count: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            count += candies[j] / mid;
            j += 1;
        }

        if count >= k {
            low = mid;
        } else {
            high = mid;
        }
    }

    low
}
