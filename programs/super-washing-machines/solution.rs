pub fn find_min_moves(machines: &[i64]) -> i64 {
    let mut n: i64 = 0;
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < machines.len() {
        total = total + machines[i];
        n = n + 1;
        i = i + 1;
    }

    if n == 0 {
        return 0;
    }

    if total % n != 0 {
        return -1;
    }

    let avg: i64 = total / n;
    let mut ans: i64 = 0;
    let mut prefix: i64 = 0;
    let mut j: usize = 0;

    while j < machines.len() {
        let diff: i64 = machines[j] - avg;
        prefix = prefix + diff;

        let mut imbalance: i64 = prefix;
        if imbalance < 0 {
            imbalance = -imbalance;
        }

        if imbalance > ans {
            ans = imbalance;
        }
        if diff > ans {
            ans = diff;
        }

        j = j + 1;
    }

    ans
}
