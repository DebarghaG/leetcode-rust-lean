pub fn get_row(rowIndex: i64) -> Vec<i64> {
    let n: usize = rowIndex as usize;
    let mut row: Vec<i64> = Vec::new();
    row.push(1);

    let mut k: usize = 1;
    while k <= n {
        let prev: i64 = row[k - 1];
        let factor: i64 = n as i64 - k as i64 + 1;
        let value: i64 = (prev * factor) / (k as i64);
        row.push(value);
        k += 1;
    }

    row
}
