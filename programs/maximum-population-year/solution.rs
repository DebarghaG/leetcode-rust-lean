pub fn maximum_population(logs: &[Vec<i64>]) -> i64 {
    // Difference array over years 1950..=2050 (101 entries).
    let mut diff: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 101 {
        diff.push(0);
        k = k + 1;
    }

    // Apply each person's birth (+1) and death (-1) events.
    let mut i: usize = 0;
    while i < logs.len() {
        let row = &logs[i];
        let birth = row[0];
        let death = row[1];
        let b_idx = (birth - 1950) as usize;
        let d_idx = (death - 1950) as usize;
        diff[b_idx] = diff[b_idx] + 1;
        diff[d_idx] = diff[d_idx] - 1;
        i = i + 1;
    }

    // Sweep the years accumulating population, tracking the first maximum.
    let mut best_year: i64 = 1950;
    let mut best_pop: i64 = -1;
    let mut cur: i64 = 0;
    let mut y: usize = 0;
    while y < 101 {
        cur = cur + diff[y];
        if cur > best_pop {
            best_pop = cur;
            best_year = 1950 + (y as i64);
        }
        y = y + 1;
    }

    best_year
}
