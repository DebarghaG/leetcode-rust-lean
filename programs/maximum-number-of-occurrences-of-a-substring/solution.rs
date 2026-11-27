const MOD_VAL: i64 = 1000000007;
const BASE_VAL: i64 = 27;

fn windows_equal(s: &[u8], a: usize, b: usize, k: usize) -> bool {
    let mut j: usize = 0;
    while j < k {
        if s[a + j] != s[b + j] {
            return false;
        }
        j += 1;
    }
    true
}

pub fn max_freq(s: &[u8], maxLetters: i64, minSize: i64, maxSize: i64) -> i64 {
    if minSize <= 0 || minSize > maxSize {
        return 0;
    }

    let n: usize = s.len();
    let k: usize = minSize as usize;

    if k > n {
        return 0;
    }

    let mut table_size: usize = 1;
    let target: usize = n * 2;
    while table_size < target {
        table_size = table_size * 2;
    }
    let mask: usize = table_size - 1;

    let mut starts: Vec<i64> = Vec::new();
    let mut freqs: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < table_size {
        starts.push(-1);
        freqs.push(0);
        t += 1;
    }

    let mut char_count: Vec<i64> = Vec::new();
    t = 0;
    while t < 26 {
        char_count.push(0);
        t += 1;
    }

    let mut unique: i64 = 0;
    let mut j: usize = 0;
    while j < k {
        let c: usize = (s[j] as i64 - 97) as usize;
        if char_count[c] == 0 {
            unique += 1;
        }
        char_count[c] += 1;
        j += 1;
    }

    let mut pow: i64 = 1;
    j = 0;
    while j + 1 < k {
        pow = (pow * BASE_VAL) % MOD_VAL;
        j += 1;
    }

    let mut h: i64 = 0;
    j = 0;
    while j < k {
        let code: i64 = s[j] as i64 - 97;
        h = (h * BASE_VAL + code) % MOD_VAL;
        j += 1;
    }

    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i + k <= n {
        if unique <= maxLetters {
            let mut pos: usize = (h as usize) & mask;
            let mut found: bool = false;
            let mut current_count: i64 = 0;

            while starts[pos] != -1 && !found {
                let cand: usize = starts[pos] as usize;
                if windows_equal(s, cand, i, k) {
                    freqs[pos] += 1;
                    current_count = freqs[pos];
                    found = true;
                } else {
                    pos = (pos + 1) & mask;
                }
            }

            if !found {
                starts[pos] = i as i64;
                freqs[pos] = 1;
                current_count = 1;
            }

            if current_count > best {
                best = current_count;
            }
        }

        if i + k < n {
            let out_byte: u8 = s[i];
            let out_idx: usize = (out_byte as i64 - 97) as usize;
            char_count[out_idx] -= 1;
            if char_count[out_idx] == 0 {
                unique -= 1;
            }

            let in_byte: u8 = s[i + k];
            let in_idx: usize = (in_byte as i64 - 97) as usize;
            if char_count[in_idx] == 0 {
                unique += 1;
            }
            char_count[in_idx] += 1;

            let out_code: i64 = out_byte as i64 - 97;
            let rem: i64 = (out_code * pow) % MOD_VAL;
            let mut h2: i64 = h - rem;
            if h2 < 0 {
                h2 += MOD_VAL;
            }

            let in_code: i64 = in_byte as i64 - 97;
            h = (h2 * BASE_VAL + in_code) % MOD_VAL;
        }

        i += 1;
    }

    best
}
