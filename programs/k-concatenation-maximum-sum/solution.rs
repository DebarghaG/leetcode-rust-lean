pub fn k_concatenation_max_sum(arr: &[i64], k: i64) -> i64 {
    const MOD: i64 = 1_000_000_007;

    let n = arr.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += arr[i];
        i += 1;
    }

    let mut prefix: i64 = 0;
    let mut running: i64 = 0;
    i = 0;
    while i < n {
        running += arr[i];
        if running > prefix {
            prefix = running;
        }
        i += 1;
    }

    let mut suffix: i64 = 0;
    running = 0;
    i = n;
    while i > 0 {
        i -= 1;
        running += arr[i];
        if running > suffix {
            suffix = running;
        }
    }

    let mut best: i64 = 0;
    let mut current: i64 = 0;
    i = 0;
    while i < n {
        current += arr[i];
        if current < 0 {
            current = 0;
        }
        if current > best {
            best = current;
        }
        i += 1;
    }

    if k == 1 {
        return best % MOD;
    }

    let mut answer = best;
    let crossing: i64;

    if total > 0 {
        crossing = suffix + total * (k - 2) + prefix;
    } else {
        crossing = suffix + prefix;
    }

    if crossing > answer {
        answer = crossing;
    }

    answer % MOD
}
