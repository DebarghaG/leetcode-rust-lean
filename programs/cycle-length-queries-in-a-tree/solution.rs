pub fn cycle_length_queries(n: i64, queries: &[Vec<i64>]) -> Vec<i64> {
    let _ = n;
    let mut answers: Vec<i64> = Vec::new();
    let m = queries.len();
    let mut i: usize = 0;

    while i < m {
        let q = &queries[i];
        let mut a: i64 = q[0];
        let mut b: i64 = q[1];
        let mut dist: i64 = 0;

        while a != b {
            if a > b {
                a = a / 2;
            } else {
                b = b / 2;
            }
            dist = dist + 1;
        }

        answers.push(dist + 1);
        i = i + 1;
    }

    answers
}
