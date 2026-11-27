fn sift_down(a: &mut Vec<i64>, mut root: usize, end: usize) {
    let mut cont = true;
    while cont {
        let left = root * 2 + 1;
        if left >= end {
            cont = false;
        } else {
            let mut child = left;
            let right = left + 1;
            if right < end {
                if a[right] > a[left] {
                    child = right;
                }
            }
            if a[child] <= a[root] {
                cont = false;
            } else {
                let tmp = a[root];
                a[root] = a[child];
                a[child] = tmp;
                root = child;
            }
        }
    }
}

fn sort_i64(a: &mut Vec<i64>) {
    let n = a.len();
    if n > 1 {
        let mut start = n / 2;
        while start > 0 {
            start -= 1;
            sift_down(a, start, n);
        }

        let mut end = n;
        while end > 1 {
            end -= 1;
            let tmp = a[0];
            a[0] = a[end];
            a[end] = tmp;
            sift_down(a, 0, end);
        }
    }
}

pub fn min_processing_time(processorTime: &[i64], tasks: &[i64]) -> i64 {
    let n = processorTime.len();
    let m = tasks.len();
    if n == 0 || m == 0 {
        return 0;
    }

    let mut p: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        p.push(processorTime[i]);
        i += 1;
    }

    let mut t: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        t.push(tasks[i]);
        i += 1;
    }

    sort_i64(&mut p);
    sort_i64(&mut t);

    let mut ans: i64 = 0;
    let mm = m as i64;
    let mut j: usize = 0;
    while j < n {
        let raw: i64 = mm - 1 - 4 * (j as i64);
        let mut idx: i64 = raw % mm;
        if idx < 0 {
            idx += mm;
        }
        let idxu = idx as usize;
        let val = p[j] + t[idxu];
        if val > ans {
            ans = val;
        }
        j += 1;
    }

    ans
}
