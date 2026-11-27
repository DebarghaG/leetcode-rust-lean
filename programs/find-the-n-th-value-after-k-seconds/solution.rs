pub fn value_after_k_seconds(n: i64, k: i64) -> i64 {
    let modulo: i64 = 1_000_000_007;
    let n_usize: usize = n as usize;
    let k_usize: usize = k as usize;

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        a.push(1);
        i += 1;
    }

    let mut sec: usize = 0;
    while sec < k_usize {
        let mut j: usize = 1;
        while j < n_usize {
            a[j] = (a[j] + a[j - 1]) % modulo;
            j += 1;
        }
        sec += 1;
    }

    a[n_usize - 1]
}
