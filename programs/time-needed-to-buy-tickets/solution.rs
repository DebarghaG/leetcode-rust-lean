pub fn time_required_to_buy(tickets: &[i64], k: i64) -> i64 {
    let n: usize = tickets.len();
    let kk: usize = k as usize;
    let target: i64 = tickets[kk];

    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if i <= kk {
            if tickets[i] < target {
                total += tickets[i];
            } else {
                total += target;
            }
        } else {
            let cap: i64 = target - 1;
            if tickets[i] < cap {
                total += tickets[i];
            } else {
                total += cap;
            }
        }

        i += 1;
    }

    total
}
