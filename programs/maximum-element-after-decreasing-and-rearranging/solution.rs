pub fn maximum_element_after_decrementing_and_rearranging(arr: &[i64]) -> i64 {
    let n = arr.len();
    let n_i64 = n as i64;

    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        counts.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let mut v = arr[i];
        if v > n_i64 {
            v = n_i64;
        }
        let idx = v as usize;
        counts[idx] += 1;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut value: usize = 1;
    while value <= n {
        let count = counts[value];
        if count > 0 {
            let candidate = ans + count;
            let upper = value as i64;
            if candidate < upper {
                ans = candidate;
            } else {
                ans = upper;
            }
        }
        value += 1;
    }

    ans
}
