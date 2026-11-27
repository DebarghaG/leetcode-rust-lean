pub fn count_seniors(details: &[Vec<u8>]) -> i64 {
    let mut count: i64 = 0;
    let n = details.len();
    let mut i: usize = 0;

    while i < n {
        let row = &details[i];

        let tens = (row[11] - b'0') as i64;
        let ones = (row[12] - b'0') as i64;
        let age = tens * 10 + ones;

        if age > 60 {
            count += 1;
        }

        i += 1;
    }

    count
}
