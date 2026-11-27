pub fn missing_rolls(rolls: &[i64], mean: i64, n: i64) -> Vec<i64> {
    let len = rolls.len();

    let mut sum_existing: i64 = 0;
    let mut m: i64 = 0;
    let mut idx: usize = 0;
    while idx < len {
        sum_existing += rolls[idx];
        m += 1;
        idx += 1;
    }

    let total_sum: i64 = mean * (n + m);
    let missing_sum: i64 = total_sum - sum_existing;

    if missing_sum < n {
        return Vec::new();
    }
    if missing_sum > 6 * n {
        return Vec::new();
    }

    let q: i64 = missing_sum / n;
    let r: i64 = missing_sum % n;

    let mut out: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n {
        if i < r {
            out.push(q + 1);
        } else {
            out.push(q);
        }
        i += 1;
    }

    out
}
