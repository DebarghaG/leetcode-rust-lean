pub fn minimum_sum(n: i64, k: i64) -> i64 {
    let half = k / 2;
    let take = if n < half { n } else { half };

    let mut sum = 0i64;
    let mut i = 1i64;
    while i <= take {
        sum += i;
        i += 1;
    }

    let remaining = n - take;
    let mut j = 0i64;
    while j < remaining {
        sum += k + j;
        j += 1;
    }

    sum
}
