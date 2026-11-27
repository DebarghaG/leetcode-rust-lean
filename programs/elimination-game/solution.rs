pub fn last_remaining(n: i64) -> i64 {
    let mut head: i64 = 1;
    let mut step: i64 = 1;
    let mut remaining: i64 = n;
    let mut left_to_right: bool = true;

    while remaining > 1 {
        if left_to_right {
            head = head + step;
        } else {
            if remaining % 2 == 1 {
                head = head + step;
            }
        }

        remaining = remaining / 2;
        step = step * 2;
        left_to_right = !left_to_right;
    }

    head
}
