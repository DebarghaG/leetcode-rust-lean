pub fn button_with_longest_time(events: &[Vec<i64>]) -> i64 {
    let mut best_index: i64 = events[0][0];
    let mut best_time: i64 = events[0][1];

    let n: usize = events.len();
    let mut i: usize = 1;

    while i < n {
        let cur_index: i64 = events[i][0];
        let cur_time: i64 = events[i][1];
        let prev_time: i64 = events[i - 1][1];
        let duration: i64 = cur_time - prev_time;

        if duration > best_time || (duration == best_time && cur_index < best_index) {
            best_time = duration;
            best_index = cur_index;
        }

        i += 1;
    }

    best_index
}
