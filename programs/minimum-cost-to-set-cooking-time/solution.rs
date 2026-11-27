pub fn min_cost_set_time(startAt: i64, moveCost: i64, pushCost: i64, targetSeconds: i64) -> i64 {
    let mut best: i64 = 1000000000;
    let mut minutes: i64 = 0;

    while minutes < 100 {
        let seconds: i64 = targetSeconds - minutes * 60;

        if seconds >= 0 && seconds <= 99 {
            let cost = digit_cost(minutes, seconds, startAt, moveCost, pushCost);
            if cost < best {
                best = cost;
            }
        }

        minutes += 1;
    }

    best
}

fn digit_cost(minutes: i64, seconds: i64, start_at: i64, move_cost: i64, push_cost: i64) -> i64 {
    let value: i64 = minutes * 100 + seconds;

    let mut divisor: i64 = 1;
    if value >= 1000 {
        divisor = 1000;
    } else if value >= 100 {
        divisor = 100;
    } else if value >= 10 {
        divisor = 10;
    }

    let mut current: i64 = start_at;
    let mut cost: i64 = 0;
    let mut remaining: i64 = value;

    while divisor > 0 {
        let digit: i64 = remaining / divisor;

        if digit != current {
            cost += move_cost;
            current = digit;
        }

        cost += push_cost;
        remaining = remaining % divisor;
        divisor = divisor / 10;
    }

    cost
}
