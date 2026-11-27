pub fn minimum_pushes(word: &[u8]) -> i64 {
    let n = word.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut cost: i64 = 1;
        let mut remaining: usize = i;

        while remaining >= 8 {
            cost += 1;
            remaining -= 8;
        }

        total += cost;
        i += 1;
    }

    total
}
