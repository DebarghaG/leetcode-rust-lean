pub fn transform_array(arr: &[i64]) -> Vec<i64> {
    let n = arr.len();
    let mut cur: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        cur.push(arr[idx]);
        idx += 1;
    }

    if n < 3 {
        return cur;
    }

    let mut changed = true;
    while changed {
        changed = false;
        let mut next: Vec<i64> = Vec::new();
        next.push(cur[0]);

        let mut i: usize = 1;
        while i + 1 < n {
            let x = cur[i];
            let left = cur[i - 1];
            let right = cur[i + 1];
            let mut y = x;

            if x < left && x < right {
                y = x + 1;
                changed = true;
            } else if x > left && x > right {
                y = x - 1;
                changed = true;
            }

            next.push(y);
            i += 1;
        }

        next.push(cur[n - 1]);
        cur = next;
    }

    cur
}
