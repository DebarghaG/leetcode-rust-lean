pub fn number_of_child(n: i64, k: i64) -> i64 {
    let period = 2 * (n - 1);
    let t = k % period;

    if t < n {
        t
    } else {
        period - t
    }
}
