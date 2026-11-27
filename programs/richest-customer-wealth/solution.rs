pub fn maximum_wealth(accounts: &[Vec<i64>]) -> i64 {
    let m = accounts.len();
    let mut best: i64 = 0;
    let mut i: usize = 0;
    while i < m {
        let row = &accounts[i];
        let n = row.len();
        let mut sum: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            sum += row[j];
            j += 1;
        }
        if sum > best {
            best = sum;
        }
        i += 1;
    }
    best
}
