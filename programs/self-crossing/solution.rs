pub fn is_self_crossing(distance: &[i64]) -> bool {
    let n = distance.len();
    let mut i: usize = 3;

    while i < n {
        if distance[i] >= distance[i - 2] && distance[i - 1] <= distance[i - 3] {
            return true;
        }

        if i >= 4 {
            if distance[i - 1] == distance[i - 3]
                && distance[i] + distance[i - 4] >= distance[i - 2]
            {
                return true;
            }
        }

        if i >= 5 {
            if distance[i - 2] >= distance[i - 4]
                && distance[i - 3] >= distance[i - 1]
                && distance[i] + distance[i - 4] >= distance[i - 2]
                && distance[i - 1] + distance[i - 5] >= distance[i - 3]
            {
                return true;
            }
        }

        i += 1;
    }

    false
}
