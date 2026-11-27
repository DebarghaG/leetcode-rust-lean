pub fn find_minimum_time(tasks: &[Vec<i64>]) -> i64 {
    let n = tasks.len();

    let mut order: Vec<i64> = Vec::new();
    let mut max_end: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        order.push(i as i64);
        let e = tasks[i][1];
        if e > max_end {
            max_end = e;
        }
        i += 1;
    }

    let mut pos: usize = 1;
    while pos < n {
        let mut j: usize = pos;
        let mut keep_moving: bool = true;
        while j > 0 && keep_moving {
            let a = order[j - 1] as usize;
            let b = order[j] as usize;
            if tasks[a][1] > tasks[b][1] {
                let tmp = order[j - 1];
                order[j - 1] = order[j];
                order[j] = tmp;
                j -= 1;
            } else {
                keep_moving = false;
            }
        }
        pos += 1;
    }

    let max_t = max_end as usize;
    let mut used: Vec<bool> = Vec::new();
    let mut u: usize = 0;
    while u < max_t + 2 {
        used.push(false);
        u += 1;
    }

    let mut answer: i64 = 0;
    let mut p: usize = 0;
    while p < n {
        let idx = order[p] as usize;
        let start = tasks[idx][0] as usize;
        let end = tasks[idx][1] as usize;
        let duration = tasks[idx][2];

        let mut already: i64 = 0;
        let mut t: usize = start;
        while t <= end {
            if used[t] {
                already += 1;
            }
            t += 1;
        }

        let mut need = duration - already;
        let mut t2: usize = end;
        while t2 >= start && need > 0 {
            if !used[t2] {
                used[t2] = true;
                need -= 1;
                answer += 1;
            }
            t2 -= 1;
        }

        p += 1;
    }

    answer
}
