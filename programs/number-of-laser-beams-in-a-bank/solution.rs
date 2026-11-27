pub fn number_of_beams(bank: &[Vec<u8>]) -> i64 {
    let m = bank.len();
    let mut total: i64 = 0;
    let mut prev: i64 = 0;
    let mut i: usize = 0;

    while i < m {
        let row = &bank[i];
        let n = row.len();
        let mut count: i64 = 0;
        let mut j: usize = 0;

        while j < n {
            if row[j] == b'1' {
                count = count + 1;
            }
            j = j + 1;
        }

        if count > 0 {
            total = total + prev * count;
            prev = count;
        }

        i = i + 1;
    }

    total
}
