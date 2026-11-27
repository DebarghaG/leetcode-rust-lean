pub fn put_marbles(weights: &[i64], k: i64) -> i64 {
    let n = weights.len();
    if k <= 1 || n <= 1 {
        return 0;
    }

    let mut sums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i + 1 < n {
        sums.push(weights[i] + weights[i + 1]);
        i += 1;
    }

    sums.sort();

    let m = (k - 1) as usize;
    let len = sums.len();

    let mut min_sum: i64 = 0;
    let mut j: usize = 0;
    while j < m {
        min_sum += sums[j];
        j += 1;
    }

    let mut max_sum: i64 = 0;
    let mut t: usize = 0;
    while t < m {
        max_sum += sums[len - m + t];
        t += 1;
    }

    max_sum - min_sum
}
