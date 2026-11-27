pub fn get_kth(lo: i64, hi: i64, k: i64) -> i64 {
    let mut vals: Vec<i64> = Vec::new();
    let mut powers: Vec<i64> = Vec::new();

    let mut x0 = lo;
    while x0 <= hi {
        let mut x = x0;
        let mut steps: i64 = 0;

        while x != 1 {
            if x % 2 == 0 {
                x = x / 2;
            } else {
                x = 3 * x + 1;
            }
            steps = steps + 1;
        }

        vals.push(x0);
        powers.push(steps);
        x0 = x0 + 1;
    }

    let n = vals.len();
    let mut i: usize = 1;

    while i < n {
        let current_power = powers[i];
        let current_value = vals[i];
        let mut j = i;

        while j > 0 {
            let prev_power = powers[j - 1];
            let prev_value = vals[j - 1];

            if prev_power > current_power
                || (prev_power == current_power && prev_value > current_value)
            {
                powers[j] = prev_power;
                vals[j] = prev_value;
                j = j - 1;
            } else {
                break;
            }
        }

        powers[j] = current_power;
        vals[j] = current_value;
        i = i + 1;
    }

    let idx = (k - 1) as usize;
    vals[idx]
}
