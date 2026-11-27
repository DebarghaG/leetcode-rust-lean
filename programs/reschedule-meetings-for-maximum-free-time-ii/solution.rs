pub fn max_free_time(eventTime: i64, startTime: &[i64], endTime: &[i64]) -> i64 {
    let n = startTime.len();
    if n == 0 {
        return eventTime;
    }

    // gaps[0]  = free time before first meeting
    // gaps[i]  = free time between meeting i-1 and meeting i
    // gaps[n]  = free time after last meeting
    let mut gaps: Vec<i64> = Vec::new();
    gaps.push(startTime[0]);

    let mut i: usize = 1;
    while i < n {
        gaps.push(startTime[i] - endTime[i - 1]);
        i += 1;
    }
    gaps.push(eventTime - endTime[n - 1]);

    let m = gaps.len(); // = n + 1

    // pre[k] = max(gaps[0..=k])  (prefix maximum, forward loop)
    let mut pre: Vec<i64> = Vec::new();
    let mut cur: i64 = -1;
    let mut k: usize = 0;
    while k < m {
        if gaps[k] > cur {
            cur = gaps[k];
        }
        pre.push(cur);
        k += 1;
    }

    // rv[t] = max(gaps[m-1-t .. m-1])  (suffix maximum stored reversed)
    let mut rv: Vec<i64> = Vec::new();
    let mut cur2: i64 = -1;
    let mut t: usize = 0;
    while t < m {
        let gi: usize = m - 1 - t;
        if gaps[gi] > cur2 {
            cur2 = gaps[gi];
        }
        rv.push(cur2);
        t += 1;
    }

    // For each meeting, compute the best free block obtained by moving it.
    let mut cand: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        let duration = endTime[idx] - startTime[idx];
        // Removing meeting idx merges gaps[idx] and gaps[idx+1].
        let base = gaps[idx] + gaps[idx + 1];

        // Largest gap whose index is neither idx nor idx+1.
        let mut best_other: i64 = -1;
        if idx > 0 {
            let a = pre[idx - 1];
            if a > best_other {
                best_other = a;
            }
        }
        if idx + 2 < m {
            let tt: usize = m - 3 - idx;
            let b = rv[tt];
            if b > best_other {
                best_other = b;
            }
        }

        let mut c = base;
        // If the moved meeting fits into another gap, the whole merged region is free.
        if best_other >= duration {
            c = base + duration;
        }
        cand.push(c);

        idx += 1;
    }

    let mut ans: i64 = 0;
    let mut p: usize = 0;
    while p < cand.len() {
        if cand[p] > ans {
            ans = cand[p];
        }
        p += 1;
    }

    ans
}
