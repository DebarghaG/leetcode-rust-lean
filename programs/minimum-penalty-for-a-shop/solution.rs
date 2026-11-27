pub fn best_closing_time(customers: &[u8]) -> i64 {
    let n = customers.len();

    let mut total_y: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if customers[i] == b'Y' {
            total_y += 1;
        }
        i += 1;
    }

    // Penalty when closing at hour 0: all customers are missed.
    let mut penalty: i64 = total_y;
    let mut best_penalty: i64 = penalty;
    let mut best_hour: i64 = 0;

    let mut j: usize = 1;
    while j <= n {
        // Move the closing hour from j-1 to j.
        // Hour j-1 becomes an open hour instead of a closed hour.
        if customers[j - 1] == b'Y' {
            penalty -= 1;
        } else {
            penalty += 1;
        }

        if penalty < best_penalty {
            best_penalty = penalty;
            best_hour = j as i64;
        }

        j += 1;
    }

    best_hour
}
