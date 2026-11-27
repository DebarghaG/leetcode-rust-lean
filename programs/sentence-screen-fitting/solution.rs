pub fn words_typing(sentence: &[Vec<u8>], rows: i64, cols: i64) -> i64 {
    let n: usize = sentence.len();
    if n == 0 || rows <= 0 || cols <= 0 {
        return 0;
    }

    let mut lens: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        lens.push(sentence[i].len() as i64);
        i += 1;
    }

    let mut next_idx: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        next_idx.push(0);
        counts.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let mut pos: i64 = 0;
        let mut idx: usize = i;
        let mut cnt: i64 = 0;
        let mut keep_going: bool = true;

        while keep_going {
            let wlen: i64 = lens[idx];
            let need: i64 = if pos == 0 { wlen } else { 1 + wlen };

            if pos + need <= cols {
                pos += need;
                idx += 1;
                if idx == n {
                    idx = 0;
                    cnt += 1;
                }
            } else {
                keep_going = false;
            }
        }

        next_idx[i] = idx as i64;
        counts[i] = cnt;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut idx: usize = 0;
    let mut r: i64 = 0;

    while r < rows {
        ans += counts[idx];
        idx = next_idx[idx] as usize;
        r += 1;
    }

    ans
}
