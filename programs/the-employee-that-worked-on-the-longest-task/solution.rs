pub fn hardest_worker(n: i64, logs: &[Vec<i64>]) -> i64 {
    let mut best_time: i64 = -1;
    let mut best_id: i64 = n;
    let mut previous_time: i64 = 0;
    let mut i: usize = 0;

    while i < logs.len() {
        let employee_id: i64 = logs[i][0];
        let leave_time: i64 = logs[i][1];
        let duration: i64 = leave_time - previous_time;

        if duration > best_time || (duration == best_time && employee_id < best_id) {
            best_time = duration;
            best_id = employee_id;
        }

        previous_time = leave_time;
        i += 1;
    }

    best_id
}
