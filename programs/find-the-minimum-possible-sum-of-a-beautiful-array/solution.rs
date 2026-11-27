pub fn minimum_possible_sum(n: i64, target: i64) -> i64 {
    let modu: i64 = 1000000007;

    let half: i64 = target / 2;
    let mut k: i64 = n;
    if half < k {
        k = half;
    }

    let q: i64 = n - k;

    let sum_low: i64 = k * (k + 1) / 2;
    let sum_high: i64 = q * (2 * target + q - 1) / 2;

    (sum_low % modu + sum_high % modu) % modu
}
