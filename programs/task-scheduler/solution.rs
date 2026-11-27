pub fn least_interval(tasks: &[Vec<u8>], n: i64) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        counts.push(0);
        i = i + 1;
    }

    let mut total: i64 = 0;
    let mut t: usize = 0;
    while t < tasks.len() {
        let label = tasks[t][0];
        let idx: usize = (label - b'A') as usize;
        counts[idx] = counts[idx] + 1;
        total = total + 1;
        t = t + 1;
    }

    if total == 0 {
        return 0;
    }

    let mut maxfreq: i64 = 0;
    let mut j: usize = 0;
    while j < 26 {
        if counts[j] > maxfreq {
            maxfreq = counts[j];
        }
        j = j + 1;
    }

    let mut max_count: i64 = 0;
    let mut k: usize = 0;
    while k < 26 {
        if counts[k] == maxfreq {
            max_count = max_count + 1;
        }
        k = k + 1;
    }

    let frame: i64 = (maxfreq - 1) * (n + 1) + max_count;
    if total > frame {
        total
    } else {
        frame
    }
}
