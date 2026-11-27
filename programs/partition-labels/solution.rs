pub fn partition_labels(s: &[u8]) -> Vec<i64> {
    let n: usize = s.len();

    let mut last: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        last.push(-1);
        k += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let b: u8 = s[i];
        let idx: usize = (b - b'a') as usize;
        last[idx] = i as i64;
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut start: i64 = 0;
    let mut end: i64 = 0;

    i = 0;
    while i < n {
        let b: u8 = s[i];
        let idx: usize = (b - b'a') as usize;
        let pos: i64 = last[idx];

        if pos > end {
            end = pos;
        }

        if (i as i64) == end {
            ans.push(end - start + 1);
            start = end + 1;
        }

        i += 1;
    }

    ans
}
