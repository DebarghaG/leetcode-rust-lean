pub fn minimum_cost(cost: &[i64]) -> i64 {
    let n = cost.len();
    if n == 0 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(cost[i]);
        i += 1;
    }

    // Sort in descending order using selection sort.
    let mut a = 0;
    while a < n {
        let mut max_idx = a;
        let mut b = a + 1;
        while b < n {
            if v[b] > v[max_idx] {
                max_idx = b;
            }
            b += 1;
        }

        if max_idx != a {
            let tmp = v[a];
            v[a] = v[max_idx];
            v[max_idx] = tmp;
        }

        a += 1;
    }

    // Buy indices 0, 1, 3, 4, 6, 7, ...
    // Every third candy, starting with index 2, is free.
    let mut total = 0;
    let mut i = 0;
    while i < n {
        total += v[i];
        if i + 1 < n {
            total += v[i + 1];
        }
        i += 3;
    }

    total
}
