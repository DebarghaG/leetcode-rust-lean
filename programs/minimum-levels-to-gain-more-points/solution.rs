pub fn minimum_levels(possible: &[i64]) -> i64 {
    let n: usize = possible.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if possible[i] == 1 {
            total += 1;
        } else {
            total -= 1;
        }
        i += 1;
    }

    let mut prefix: i64 = 0;
    let mut count: i64 = 0;
    i = 0;

    while i < n {
        if possible[i] == 1 {
            prefix += 1;
        } else {
            prefix -= 1;
        }
        count += 1;

        if i + 1 < n && 2 * prefix > total {
            return count;
        }

        i += 1;
    }

    -1
}
