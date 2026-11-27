pub fn corp_flight_bookings(bookings: &[Vec<i64>], n: i64) -> Vec<i64> {
    let mut diff: Vec<i64> = Vec::new();
    let mut k: i64 = 0;
    while k <= n {
        diff.push(0);
        k += 1;
    }

    let m = bookings.len();
    let mut i: usize = 0;
    while i < m {
        let booking = &bookings[i];
        let first = booking[0];
        let last = booking[1];
        let seats = booking[2];

        let start = (first - 1) as usize;
        let end = last as usize;

        diff[start] = diff[start] + seats;
        diff[end] = diff[end] - seats;

        i += 1;
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut current: i64 = 0;
    let mut j: i64 = 0;
    while j < n {
        let idx = j as usize;
        current = current + diff[idx];
        answer.push(current);
        j += 1;
    }

    answer
}
