pub fn max_happy_groups(batchSize: i64, groups: &[i64]) -> i64 {
    let b: usize = batchSize as usize;

    let mut cnt: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < b {
        cnt.push(0);
        i += 1;
    }

    let mut base_happy: i64 = 0;
    let mut idx: usize = 0;
    while idx < groups.len() {
        let rem: usize = (groups[idx] % batchSize) as usize;
        if rem == 0 {
            base_happy += 1;
        } else {
            cnt[rem] += 1;
        }
        idx += 1;
    }

    if b == 1 {
        return base_happy;
    }

    let b_i: i64 = batchSize;

    let mut total_sum_mod: i64 = 0;
    let mut r: usize = 1;
    while r < b {
        total_sum_mod = (total_sum_mod + cnt[r] * (r as i64)) % b_i;
        r += 1;
    }

    let mut stride: Vec<i64> = Vec::new();
    i = 0;
    while i < b {
        stride.push(0);
        i += 1;
    }

    let mut total_states: i64 = 1;
    r = 1;
    while r < b {
        stride[r] = total_states;
        total_states = total_states * (cnt[r] + 1);
        r += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut p: i64 = 0;
    while p < total_states {
        dp.push(0);
        p += 1;
    }

    let mut code: i64 = 1;
    while code < total_states {
        let mut r_mod: i64 = 0;
        let mut best_prev: i64 = 0;

        let mut rem_i: usize = 1;
        while rem_i < b {
            let stride_i: i64 = stride[rem_i];
            let digit: i64 = (code / stride_i) % (cnt[rem_i] + 1);

            if digit > 0 {
                r_mod += digit * (rem_i as i64);
                let prev_val: i64 = dp[(code - stride_i) as usize];
                if prev_val > best_prev {
                    best_prev = prev_val;
                }
            }

            rem_i += 1;
        }

        let mut gain: i64 = 0;
        if r_mod % b_i == total_sum_mod {
            gain = 1;
        }

        dp[code as usize] = best_prev + gain;
        code += 1;
    }

    let full_code: i64 = total_states - 1;
    base_happy + dp[full_code as usize]
}
