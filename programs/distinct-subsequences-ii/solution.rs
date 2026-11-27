pub fn distinct_subseq_ii(s: &[u8]) -> i64 {
    const MOD: i64 = 1_000_000_007;

    let mut last: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        last.push(0);
        i += 1;
    }

    let mut total: i64 = 0;
    let n = s.len();
    let mut pos: usize = 0;
    while pos < n {
        let idx: usize = (s[pos] - b'a') as usize;

        let old_total = total;
        let mut new_total = (2 * old_total + 1) % MOD - last[idx];
        if new_total < 0 {
            new_total += MOD;
        }
        total = new_total;

        let mut new_ending = old_total + 1;
        if new_ending >= MOD {
            new_ending -= MOD;
        }
        last[idx] = new_ending;

        pos += 1;
    }

    total
}
