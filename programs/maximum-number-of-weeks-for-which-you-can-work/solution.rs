pub fn number_of_weeks(milestones: &[i64]) -> i64 {
    let n = milestones.len();
    let mut total: i64 = 0;
    let mut max_val: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let v = milestones[i];
        total += v;
        if v > max_val {
            max_val = v;
        }
        i += 1;
    }

    let rest = total - max_val;
    if max_val > rest + 1 {
        2 * rest + 1
    } else {
        total
    }
}
