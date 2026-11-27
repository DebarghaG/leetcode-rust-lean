pub fn share_candies(candies: &[i64], k: i64) -> i64 {
    let n = candies.len();
    if n == 0 {
        return 0;
    }

    let kk = k as usize;

    let mut max_value: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if candies[i] > max_value {
            max_value = candies[i];
        }
        i += 1;
    }

    let m = (max_value as usize) + 1;
    let mut total: Vec<i64> = Vec::new();
    let mut window: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < m {
        total.push(0);
        window.push(0);
        j += 1;
    }

    let mut unique_total: i64 = 0;
    i = 0;
    while i < n {
        let v = candies[i] as usize;
        if total[v] == 0 {
            unique_total += 1;
        }
        total[v] += 1;
        i += 1;
    }

    if kk == 0 {
        return unique_total;
    }

    if kk >= n {
        return 0;
    }

    let mut fully_removed: i64 = 0;
    i = 0;
    while i < kk {
        let v = candies[i] as usize;
        window[v] += 1;
        if window[v] == total[v] {
            fully_removed += 1;
        }
        i += 1;
    }

    let mut best = unique_total - fully_removed;

    let mut left: usize = 0;
    let mut right: usize = kk;

    while right < n {
        let vl = candies[left] as usize;
        if window[vl] == total[vl] {
            fully_removed -= 1;
        }
        window[vl] -= 1;

        let vr = candies[right] as usize;
        window[vr] += 1;
        if window[vr] == total[vr] {
            fully_removed += 1;
        }

        left += 1;
        right += 1;

        let kept = unique_total - fully_removed;
        if kept > best {
            best = kept;
        }
    }

    best
}
