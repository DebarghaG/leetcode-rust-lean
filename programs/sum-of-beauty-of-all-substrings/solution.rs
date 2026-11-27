pub fn beauty_sum(s: &[u8]) -> i64 {
    let n = s.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut cnt: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < 26 {
            cnt.push(0);
            k += 1;
        }

        let mut j: usize = i;
        while j < n {
            let idx: usize = (s[j] - b'a') as usize;
            cnt[idx] = cnt[idx] + 1;

            let mut maxf: i64 = 0;
            let mut minf: i64 = 1000000000;
            let mut c: usize = 0;

            while c < 26 {
                let v = cnt[c];
                if v > 0 {
                    if v > maxf {
                        maxf = v;
                    }
                    if v < minf {
                        minf = v;
                    }
                }
                c += 1;
            }

            total = total + (maxf - minf);
            j += 1;
        }

        i += 1;
    }

    total
}
