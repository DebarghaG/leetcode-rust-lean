pub fn find_original_array(changed: &[i64]) -> Vec<i64> {
    let n = changed.len();
    let mut result: Vec<i64> = Vec::new();

    if n % 2 != 0 {
        return result;
    }
    if n == 0 {
        return result;
    }

    // Find maximum value; also validate non-negative.
    let mut max_val: i64 = 0;
    let mut ok_input: bool = true;
    let mut i: usize = 0;
    while i < n {
        if changed[i] < 0 {
            ok_input = false;
        }
        if changed[i] > max_val {
            max_val = changed[i];
        }
        i += 1;
    }
    if !ok_input {
        return result;
    }

    // Build frequency counts.
    let size: usize = (max_val as usize) + 1;
    let mut counts: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < size {
        counts.push(0);
        j += 1;
    }

    i = 0;
    while i < n {
        let v = changed[i] as usize;
        counts[v] = counts[v] + 1;
        i += 1;
    }

    // Process values in increasing order.
    let mut ok: bool = true;
    let mut x: i64 = 0;
    while x <= max_val {
        let xi = x as usize;

        if x == 0 {
            let c0 = counts[xi];
            if c0 % 2 != 0 {
                ok = false;
            } else {
                let half = c0 / 2;
                let mut t: i64 = 0;
                while t < half {
                    result.push(0);
                    t += 1;
                }
                counts[xi] = 0;
            }
        } else {
            let c = counts[xi];
            if c > 0 {
                let d = x * 2;
                if d > max_val {
                    ok = false;
                } else {
                    let di = d as usize;
                    if counts[di] < c {
                        ok = false;
                    } else {
                        let mut t: i64 = 0;
                        while t < c {
                            result.push(x);
                            t += 1;
                        }
                        counts[di] = counts[di] - c;
                        counts[xi] = 0;
                    }
                }
            }
        }

        x += 1;
    }

    if !ok {
        return Vec::new();
    }

    result
}
