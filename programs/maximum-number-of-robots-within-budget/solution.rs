pub fn maximum_robots(chargeTimes: &[i64], runningCosts: &[i64], budget: i64) -> i64 {
    let n = chargeTimes.len();
    if n == 0 {
        return 0;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut sum_running: i64 = 0;
    let mut best: i64 = 0;

    // Stores indices of chargeTimes in decreasing charge order.
    // `head` marks the first active element; earlier entries are stale.
    let mut dq: Vec<i64> = Vec::new();
    let mut head: usize = 0;

    while right < n {
        sum_running += runningCosts[right];

        let cur_charge = chargeTimes[right];
        while dq.len() > head {
            let last_index = dq[dq.len() - 1] as usize;
            if chargeTimes[last_index] <= cur_charge {
                dq.pop();
            } else {
                break;
            }
        }
        dq.push(right as i64);

        while left <= right {
            let max_index = dq[head] as usize;
            let k = (right - left + 1) as i64;
            let cost = chargeTimes[max_index] + k * sum_running;

            if cost <= budget {
                break;
            }

            sum_running -= runningCosts[left];
            left += 1;

            while head < dq.len() && (dq[head] as usize) < left {
                head += 1;
            }
        }

        if left <= right {
            let len = (right - left + 1) as i64;
            if len > best {
                best = len;
            }
        }

        right += 1;
    }

    best
}
