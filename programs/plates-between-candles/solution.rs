pub fn plates_between_candles(s: &[u8], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = s.len();

    // pref[i] = number of plates in s[0..i]
    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);
    let mut i = 0;
    while i < n {
        let mut val = pref[i];
        if s[i] == b'*' {
            val += 1;
        }
        pref.push(val);
        i += 1;
    }

    // next[i] = first candle index >= i, or n if none
    let mut next: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < n {
        next.push(n as i64);
        k += 1;
    }

    let mut last = n as i64;
    let mut i2 = n;
    while i2 > 0 {
        i2 -= 1;
        if s[i2] == b'|' {
            last = i2 as i64;
        }
        next[i2] = last;
    }

    // prev[i] = last candle index <= i, or -1 if none
    let mut prev: Vec<i64> = Vec::new();
    let mut k2 = 0;
    while k2 < n {
        prev.push(-1);
        k2 += 1;
    }

    let mut last2: i64 = -1;
    let mut i3 = 0;
    while i3 < n {
        if s[i3] == b'|' {
            last2 = i3 as i64;
        }
        prev[i3] = last2;
        i3 += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let qn = queries.len();
    let mut qi = 0;
    while qi < qn {
        let left = queries[qi][0];
        let right = queries[qi][1];

        let l = left as usize;
        let r = right as usize;

        let cl = next[l];
        let cr = prev[r];

        if cl > right || cr < left || cl >= cr {
            ans.push(0);
        } else {
            let plates = pref[cr as usize] - pref[cl as usize];
            ans.push(plates);
        }

        qi += 1;
    }

    ans
}
