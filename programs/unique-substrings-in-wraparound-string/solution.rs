pub fn find_substring_in_wrapround_string(s: &[u8]) -> i64 {
    let n: usize = s.len();
    if n == 0 {
        return 0;
    }

    let mut max_len: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        max_len.push(0);
        k += 1;
    }

    let first: u8 = s[0];
    let first_idx: usize = (first - b'a') as usize;
    max_len[first_idx] = 1;

    let mut cur: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        let prev: u8 = s[i - 1];
        let c: u8 = s[i];

        let mut follows: bool = false;
        if prev == b'z' {
            if c == b'a' {
                follows = true;
            }
        } else {
            if c == prev + 1 {
                follows = true;
            }
        }

        if follows {
            cur = cur + 1;
        } else {
            cur = 1;
        }

        let idx: usize = (c - b'a') as usize;
        if cur > max_len[idx] {
            max_len[idx] = cur;
        }

        i += 1;
    }

    let mut total: i64 = 0;
    let mut j: usize = 0;
    while j < 26 {
        total += max_len[j];
        j += 1;
    }

    total
}
