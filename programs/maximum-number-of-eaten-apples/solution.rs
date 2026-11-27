fn push_apple(heap_exp: &mut Vec<i64>, heap_cnt: &mut Vec<i64>, exp: i64, cnt: i64) {
    heap_exp.push(exp);
    heap_cnt.push(cnt);

    let mut i = heap_exp.len() - 1;
    while i > 0 {
        let p = (i - 1) / 2;
        if heap_exp[p] <= heap_exp[i] {
            break;
        }

        let te = heap_exp[p];
        heap_exp[p] = heap_exp[i];
        heap_exp[i] = te;

        let tc = heap_cnt[p];
        heap_cnt[p] = heap_cnt[i];
        heap_cnt[i] = tc;

        i = p;
    }
}

fn pop_min(heap_exp: &mut Vec<i64>, heap_cnt: &mut Vec<i64>) {
    let len = heap_exp.len();
    if len == 0 {
        return;
    }

    if len == 1 {
        heap_exp.pop();
        heap_cnt.pop();
        return;
    }

    let last = len - 1;
    heap_exp[0] = heap_exp[last];
    heap_cnt[0] = heap_cnt[last];
    heap_exp.pop();
    heap_cnt.pop();

    let n = heap_exp.len();
    let mut i: usize = 0;
    let mut done = false;

    while !done {
        let l = 2 * i + 1;
        let r = 2 * i + 2;
        let mut m = i;

        if l < n && heap_exp[l] < heap_exp[m] {
            m = l;
        }
        if r < n && heap_exp[r] < heap_exp[m] {
            m = r;
        }

        if m == i {
            done = true;
        } else {
            let te = heap_exp[i];
            heap_exp[i] = heap_exp[m];
            heap_exp[m] = te;

            let tc = heap_cnt[i];
            heap_cnt[i] = heap_cnt[m];
            heap_cnt[m] = tc;

            i = m;
        }
    }
}

pub fn eaten_apples(apples: &[i64], days: &[i64]) -> i64 {
    let n = apples.len();
    let mut heap_exp: Vec<i64> = Vec::new();
    let mut heap_cnt: Vec<i64> = Vec::new();

    let mut eaten: i64 = 0;
    let mut day: i64 = 0;

    while day < n as i64 || heap_exp.len() > 0 {
        if day < n as i64 {
            let i = day as usize;
            if apples[i] > 0 {
                push_apple(&mut heap_exp, &mut heap_cnt, day + days[i], apples[i]);
            }
        }

        while heap_exp.len() > 0 && heap_exp[0] <= day {
            pop_min(&mut heap_exp, &mut heap_cnt);
        }

        if heap_exp.len() > 0 {
            heap_cnt[0] = heap_cnt[0] - 1;
            eaten = eaten + 1;

            if heap_cnt[0] == 0 {
                pop_min(&mut heap_exp, &mut heap_cnt);
            }
        }

        day = day + 1;
    }

    eaten
}
