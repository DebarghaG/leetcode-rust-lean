pub fn find_kth_number(n: i64, k: i64) -> i64 {
    let mut current: i64 = 1;
    let mut remaining: i64 = k;

    while remaining > 1 {
        let count: i64 = count_subtree(current, n);

        if remaining > count {
            remaining = remaining - count;
            current = current + 1;
        } else {
            remaining = remaining - 1;
            current = current * 10;
        }
    }

    current
}

fn count_subtree(prefix: i64, n: i64) -> i64 {
    let mut count: i64 = 0;
    let mut first: i64 = prefix;
    let mut next: i64 = prefix + 1;
    let limit: i64 = n + 1;

    while first <= n {
        let upper: i64 = if next <= limit { next } else { limit };
        count = count + (upper - first);
        first = first * 10;
        next = next * 10;
    }

    count
}
