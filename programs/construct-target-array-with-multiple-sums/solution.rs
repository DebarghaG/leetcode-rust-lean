pub fn is_possible(target: &[i64]) -> bool {
    let n = target.len();

    let mut a: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let v = target[i];
        a.push(v);
        sum = sum + v;
        i += 1;
    }

    if n == 0 {
        return false;
    }

    if n == 1 {
        return a[0] == 1;
    }

    loop {
        let mut max_idx: usize = 0;
        let mut max_val: i64 = a[0];
        let mut j: usize = 1;

        while j < n {
            let v = a[j];
            if v > max_val {
                max_val = v;
                max_idx = j;
            }
            j += 1;
        }

        if max_val == 1 {
            return true;
        }

        let rest = sum - max_val;

        if rest <= 0 {
            return false;
        }

        if max_val <= rest {
            return false;
        }

        let k = (max_val - 1) / rest;
        let new_val = max_val - k * rest;

        if new_val <= 0 {
            return false;
        }

        a[max_idx] = new_val;
        sum = sum - max_val + new_val;
    }
}
