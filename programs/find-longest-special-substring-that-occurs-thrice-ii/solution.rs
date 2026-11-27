pub fn maximum_length(s: &[u8]) -> i64 {
    let n: usize = s.len();

    let mut top1: Vec<i64> = Vec::new();
    let mut top2: Vec<i64> = Vec::new();
    let mut top3: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        top1.push(0);
        top2.push(0);
        top3.push(0);
        i += 1;
    }

    let mut pos: usize = 0;
    while pos < n {
        let c: u8 = s[pos];
        let mut end: usize = pos + 1;
        while end < n && s[end] == c {
            end += 1;
        }

        let len: i64 = (end - pos) as i64;
        let idx: usize = (c as usize) - 97;

        if len > top1[idx] {
            top3[idx] = top2[idx];
            top2[idx] = top1[idx];
            top1[idx] = len;
        } else if len > top2[idx] {
            top3[idx] = top2[idx];
            top2[idx] = len;
        } else if len > top3[idx] {
            top3[idx] = len;
        }

        pos = end;
    }

    let mut answer: i64 = -1;
    let mut ch: usize = 0;

    while ch < 26 {
        let a: i64 = top1[ch];
        let b: i64 = top2[ch];
        let c: i64 = top3[ch];

        let mut best: i64 = 0;

        if a - 2 > best {
            best = a - 2;
        }

        let sum_ab: i64 = a + b - 1;
        if sum_ab > 0 {
            let mut cand: i64 = sum_ab / 2;
            if b < cand {
                cand = b;
            }
            if cand > best {
                best = cand;
            }
        }

        if c > best {
            best = c;
        }

        if best > answer {
            answer = best;
        }

        ch += 1;
    }

    if answer < 1 {
        -1
    } else {
        answer
    }
}
