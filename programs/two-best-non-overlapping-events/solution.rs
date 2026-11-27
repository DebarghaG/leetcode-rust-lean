fn event_leq(events: &[Vec<i64>], a: usize, b: usize) -> bool {
    let end_a = events[a][1];
    let end_b = events[b][1];
    if end_a < end_b {
        return true;
    }
    if end_a > end_b {
        return false;
    }

    let start_a = events[a][0];
    let start_b = events[b][0];
    if start_a < start_b {
        return true;
    }
    if start_a > start_b {
        return false;
    }

    events[a][2] <= events[b][2]
}

pub fn max_two_events(events: &[Vec<i64>]) -> i64 {
    let n = events.len();
    if n == 0 {
        return 0;
    }

    let mut order: Vec<usize> = Vec::new();
    let mut i = 0usize;
    while i < n {
        order.push(i);
        i += 1;
    }

    let mut buf: Vec<usize> = Vec::new();
    i = 0;
    while i < n {
        buf.push(0);
        i += 1;
    }

    let mut width = 1usize;
    while width < n {
        let two_width = width + width;
        i = 0;
        while i < n {
            let mid = if i + width < n { i + width } else { n };
            let high = if i + two_width < n { i + two_width } else { n };

            let mut left = i;
            let mut right = mid;
            let mut out = i;

            while left < mid && right < high {
                let a = order[left];
                let b = order[right];
                if event_leq(events, a, b) {
                    buf[out] = a;
                    left += 1;
                } else {
                    buf[out] = b;
                    right += 1;
                }
                out += 1;
            }

            while left < mid {
                buf[out] = order[left];
                left += 1;
                out += 1;
            }

            while right < high {
                buf[out] = order[right];
                right += 1;
                out += 1;
            }

            i = high;
        }

        let mut j = 0usize;
        while j < n {
            order[j] = buf[j];
            j += 1;
        }

        width = width + width;
    }

    let mut prefix: Vec<i64> = Vec::new();
    let mut best = 0i64;
    i = 0;
    while i < n {
        let idx = order[i];
        let value = events[idx][2];
        if value > best {
            best = value;
        }
        prefix.push(best);
        i += 1;
    }

    let mut ans = 0i64;
    let mut p = 0usize;
    while p < n {
        let idx = order[p];
        let start = events[idx][0];
        let value = events[idx][2];

        if value > ans {
            ans = value;
        }

        let mut lo = 0usize;
        let mut hi = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let mid_idx = order[mid];
            if events[mid_idx][1] < start {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo > 0 {
            let candidate = value + prefix[lo - 1];
            if candidate > ans {
                ans = candidate;
            }
        }

        p += 1;
    }

    ans
}
