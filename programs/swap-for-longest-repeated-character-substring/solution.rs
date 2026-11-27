pub fn max_rep_opt1(text: &[u8]) -> i64 {
    let n: usize = text.len();
    if n == 0 {
        return 0;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        counts.push(0);
        k += 1;
    }

    let mut p: usize = 0;
    while p < n {
        let idx: usize = (text[p] - b'a') as usize;
        let cur: i64 = counts[idx];
        counts[idx] = cur + 1;
        p += 1;
    }

    let mut ans: i64 = 0;
    let mut c: usize = 0;
    while c < 26 {
        let target: u8 = b'a' + (c as u8);
        let total: i64 = counts[c];

        let mut i: usize = 0;
        let mut prev_len: i64 = 0;
        let mut prev_end: usize = 0;
        let mut has_prev: bool = false;

        while i < n {
            if text[i] == target {
                let start: usize = i;

                while i < n && text[i] == target {
                    i += 1;
                }

                let len: i64 = (i - start) as i64;

                let mut cand: i64 = len;
                if total > len {
                    cand = cand + 1;
                }
                if cand > ans {
                    ans = cand;
                }

                if has_prev && start == prev_end + 1 {
                    let mut merged: i64 = prev_len + len;
                    if total > merged {
                        merged = merged + 1;
                    }
                    if merged > ans {
                        ans = merged;
                    }
                }

                has_prev = true;
                prev_len = len;
                prev_end = i;
            } else {
                i += 1;
            }
        }

        c += 1;
    }

    ans
}
