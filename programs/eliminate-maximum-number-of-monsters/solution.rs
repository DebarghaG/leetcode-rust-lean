pub fn eliminate_maximum(dist: &[i64], speed: &[i64]) -> i64 {
    let n = dist.len();

    // Find the maximum arrival time so we can size a counting array.
    let mut max_time: usize = 0;
    let mut i: usize = 0;
    while i < n {
        let d = dist[i];
        let s = speed[i];
        let t_i64 = (d + s - 1) / s; // ceil(d / s)
        let t = t_i64 as usize;
        if t > max_time {
            max_time = t;
        }
        i += 1;
    }

    let len = max_time + 1;

    // counts[t] = number of monsters that arrive at time t.
    let mut counts: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < len {
        counts.push(0);
        j += 1;
    }

    i = 0;
    while i < n {
        let d = dist[i];
        let s = speed[i];
        let t_i64 = (d + s - 1) / s;
        let t = t_i64 as usize;
        let cur = counts[t];
        counts[t] = cur + 1;
        i += 1;
    }

    // Greedily process arrival groups in increasing time order, in ONE loop.
    // `killed` is both the number killed so far and the next kill minute.
    let mut killed: i64 = 0;
    let mut t: usize = 0;
    while t < len {
        let c = counts[t];
        let ti = t as i64;
        let mut avail = ti - killed;
        if avail < 0 {
            avail = 0;
        }
        let mut take = avail;
        if c < take {
            take = c;
        }
        killed += take;
        if take < c {
            // Not all of this group can be killed -> game effectively ends.
            t = len;
        } else {
            t += 1;
        }
    }

    killed
}
