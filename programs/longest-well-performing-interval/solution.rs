pub fn longest_wpi(hours: &[i64]) -> i64 {
    let n: usize = hours.len();

    let mut pref: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    pref.push(sum);

    let mut i: usize = 0;
    while i < n {
        if hours[i] > 8 {
            sum += 1;
        } else {
            sum -= 1;
        }
        pref.push(sum);
        i += 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    i = 0;
    while i <= n {
        let stack_len: usize = stack.len();
        if stack_len == 0 {
            stack.push(i as i64);
        } else {
            let last: usize = stack[stack_len - 1] as usize;
            if pref[i] < pref[last] {
                stack.push(i as i64);
            }
        }
        i += 1;
    }

    let mut best: i64 = 0;
    let mut top: usize = stack.len();
    let mut j_plus_one: usize = n + 1;

    while j_plus_one > 0 {
        j_plus_one -= 1;
        let j: usize = j_plus_one;

        while top > 0 {
            let sidx_i64: i64 = stack[top - 1];
            let sidx: usize = sidx_i64 as usize;

            if pref[j] > pref[sidx] {
                let len: i64 = j as i64 - sidx_i64;
                if len > best {
                    best = len;
                }
                top -= 1;
            } else {
                break;
            }
        }
    }

    best
}
