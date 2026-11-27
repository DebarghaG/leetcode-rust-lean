pub fn task_scheduler_ii(tasks: &[i64], space: i64) -> i64 {
    let n: usize = tasks.len();

    let mut cap: usize = 1;
    let target: usize = 2 * n;
    while cap < target {
        cap = cap * 2;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut lasts: Vec<i64> = Vec::new();
    let mut init: usize = 0;
    while init < cap {
        keys.push(-1);
        lasts.push(0);
        init = init + 1;
    }

    let cap_i64: i64 = cap as i64;
    let mut day: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let t: i64 = tasks[i];

        let mut h: i64 = t;
        h = h ^ (h >> 16);
        h = h * 73244475;
        h = h ^ (h >> 16);
        h = h % cap_i64;

        let mut pos: usize = h as usize;
        while keys[pos] != -1 && keys[pos] != t {
            pos = pos + 1;
            if pos == cap {
                pos = 0;
            }
        }

        if keys[pos] == -1 {
            keys[pos] = t;
        }

        let last: i64 = lasts[pos];
        let mut cur: i64 = day + 1;

        if last > 0 {
            let earliest: i64 = last + space + 1;
            if cur < earliest {
                cur = earliest;
            }
        }

        lasts[pos] = cur;
        day = cur;
        i = i + 1;
    }

    day
}
