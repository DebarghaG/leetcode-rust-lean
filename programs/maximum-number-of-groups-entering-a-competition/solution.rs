pub fn maximum_groups(grades: &[i64]) -> i64 {
    let n = grades.len() as i64;
    let mut k: i64 = 0;

    while (k + 1) * (k + 2) / 2 <= n {
        k = k + 1;
    }

    k
}
