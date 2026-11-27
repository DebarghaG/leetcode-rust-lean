fn prefix_sum(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let mut sum: i64 = 0;
    let mut p: i64 = 1;
    let mut level: i64 = 1;

    while p <= n {
        let mut hi: i64 = p * 4 - 1;
        if hi > n {
            hi = n;
        }

        if hi >= p {
            sum = sum + (hi - p + 1) * level;
        }

        p = p * 4;
        level = level + 1;
    }

    sum
}

pub fn min_operations(queries: &[Vec<i64>]) -> i64 {
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < queries.len() {
        let l: i64 = queries[i][0];
        let r: i64 = queries[i][1];

        let required: i64 = prefix_sum(r) - prefix_sum(l - 1);
        total = total + (required + 1) / 2;

        i = i + 1;
    }

    total
}
