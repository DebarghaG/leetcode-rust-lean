fn free_less(a_weight: i64, a_idx: i64, b_weight: i64, b_idx: i64) -> bool {
    if a_weight < b_weight {
        return true;
    }
    if a_weight > b_weight {
        return false;
    }
    a_idx < b_idx
}

fn free_push(weights: &mut Vec<i64>, indices: &mut Vec<i64>, w: i64, idx: i64) {
    weights.push(w);
    indices.push(idx);
    let mut i = weights.len() - 1;
    while i > 0 {
        let parent = (i - 1) / 2;
        let wi = weights[i];
        let ii = indices[i];
        let wp = weights[parent];
        let ip = indices[parent];
        if free_less(wi, ii, wp, ip) {
            weights[i] = wp;
            indices[i] = ip;
            weights[parent] = wi;
            indices[parent] = ii;
            i = parent;
        } else {
            break;
        }
    }
}

fn free_pop(weights: &mut Vec<i64>, indices: &mut Vec<i64>) {
    let old_len = weights.len();
    if old_len == 1 {
        let _ = weights.pop();
        let _ = indices.pop();
        return;
    }

    let last_w = weights[old_len - 1];
    let last_i = indices[old_len - 1];
    let _ = weights.pop();
    let _ = indices.pop();

    weights[0] = last_w;
    indices[0] = last_i;

    let n = weights.len();
    let mut i: usize = 0;
    loop {
        let left = 2 * i + 1;
        if left >= n {
            break;
        }
        let right = left + 1;
        let mut child = left;

        if right < n {
            let lw = weights[left];
            let li = indices[left];
            let rw = weights[right];
            let ri = indices[right];
            if free_less(rw, ri, lw, li) {
                child = right;
            }
        }

        let cw = weights[child];
        let ci = indices[child];
        let pw = weights[i];
        let pi = indices[i];

        if free_less(cw, ci, pw, pi) {
            weights[child] = pw;
            indices[child] = pi;
            weights[i] = cw;
            indices[i] = ci;
            i = child;
        } else {
            break;
        }
    }
}

fn busy_less(
    a_time: i64,
    a_weight: i64,
    a_idx: i64,
    b_time: i64,
    b_weight: i64,
    b_idx: i64,
) -> bool {
    if a_time < b_time {
        return true;
    }
    if a_time > b_time {
        return false;
    }
    if a_idx < b_idx {
        return true;
    }
    if a_idx > b_idx {
        return false;
    }
    a_weight < b_weight
}

fn busy_push(
    times: &mut Vec<i64>,
    weights: &mut Vec<i64>,
    indices: &mut Vec<i64>,
    t: i64,
    w: i64,
    idx: i64,
) {
    times.push(t);
    weights.push(w);
    indices.push(idx);

    let mut i = times.len() - 1;
    while i > 0 {
        let parent = (i - 1) / 2;

        let ti = times[i];
        let wi = weights[i];
        let ii = indices[i];

        let tp = times[parent];
        let wp = weights[parent];
        let ip = indices[parent];

        if busy_less(ti, wi, ii, tp, wp, ip) {
            times[i] = tp;
            weights[i] = wp;
            indices[i] = ip;

            times[parent] = ti;
            weights[parent] = wi;
            indices[parent] = ii;

            i = parent;
        } else {
            break;
        }
    }
}

fn busy_pop(times: &mut Vec<i64>, weights: &mut Vec<i64>, indices: &mut Vec<i64>) {
    let old_len = times.len();
    if old_len == 1 {
        let _ = times.pop();
        let _ = weights.pop();
        let _ = indices.pop();
        return;
    }

    let last_t = times[old_len - 1];
    let last_w = weights[old_len - 1];
    let last_i = indices[old_len - 1];

    let _ = times.pop();
    let _ = weights.pop();
    let _ = indices.pop();

    times[0] = last_t;
    weights[0] = last_w;
    indices[0] = last_i;

    let n = times.len();
    let mut i: usize = 0;
    loop {
        let left = 2 * i + 1;
        if left >= n {
            break;
        }
        let right = left + 1;
        let mut child = left;

        if right < n {
            let lt = times[left];
            let lw = weights[left];
            let li = indices[left];

            let rt = times[right];
            let rw = weights[right];
            let ri = indices[right];

            if busy_less(rt, rw, ri, lt, lw, li) {
                child = right;
            }
        }

        let ct = times[child];
        let cw = weights[child];
        let ci = indices[child];

        let pt = times[i];
        let pw = weights[i];
        let pi = indices[i];

        if busy_less(ct, cw, ci, pt, pw, pi) {
            times[child] = pt;
            weights[child] = pw;
            indices[child] = pi;

            times[i] = ct;
            weights[i] = cw;
            indices[i] = ci;

            i = child;
        } else {
            break;
        }
    }
}

pub fn assign_tasks(servers: &[i64], tasks: &[i64]) -> Vec<i64> {
    let n = servers.len();
    let m = tasks.len();

    let mut free_w: Vec<i64> = Vec::new();
    let mut free_i: Vec<i64> = Vec::new();

    let mut busy_t: Vec<i64> = Vec::new();
    let mut busy_w: Vec<i64> = Vec::new();
    let mut busy_i: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        free_push(&mut free_w, &mut free_i, servers[i], i as i64);
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut now: i64 = 0;
    let mut j: usize = 0;

    while j < m {
        let jj = j as i64;
        if jj > now {
            now = jj;
        }

        while busy_t.len() > 0 && busy_t[0] <= now {
            let w = busy_w[0];
            let idx = busy_i[0];
            busy_pop(&mut busy_t, &mut busy_w, &mut busy_i);
            free_push(&mut free_w, &mut free_i, w, idx);
        }

        if free_w.len() == 0 {
            now = busy_t[0];

            while busy_t.len() > 0 && busy_t[0] <= now {
                let w = busy_w[0];
                let idx = busy_i[0];
                busy_pop(&mut busy_t, &mut busy_w, &mut busy_i);
                free_push(&mut free_w, &mut free_i, w, idx);
            }
        }

        let w = free_w[0];
        let idx = free_i[0];
        free_pop(&mut free_w, &mut free_i);

        ans.push(idx);
        busy_push(&mut busy_t, &mut busy_w, &mut busy_i, now + tasks[j], w, idx);

        j += 1;
    }

    ans
}
