pub fn min_set_size(arr: &[i64]) -> i64 {
    let n: usize = arr.len();
    if n == 0 {
        return 0;
    }

    let mut maxv: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let x = arr[i];
        if x > maxv {
            maxv = x;
        }
        i += 1;
    }

    let m: usize = (maxv + 1) as usize;
    let mut counts: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        counts.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let x = arr[i];
        let idx: usize = x as usize;
        counts[idx] = counts[idx] + 1;
        i += 1;
    }

    let mut freq: Vec<i64> = Vec::new();
    i = 0;
    while i <= n {
        freq.push(0);
        i += 1;
    }

    i = 0;
    while i < counts.len() {
        let c: i64 = counts[i];
        if c > 0 {
            let ci: usize = c as usize;
            freq[ci] = freq[ci] + 1;
        }
        i += 1;
    }

    let target: i64 = ((n as i64) + 1) / 2;
    let mut removed: i64 = 0;
    let mut ans: i64 = 0;

    let mut f: i64 = n as i64;
    while f >= 1 {
        let mut c: i64 = freq[f as usize];
        while c > 0 && removed < target {
            removed = removed + f;
            ans = ans + 1;
            c = c - 1;
        }
        f = f - 1;
    }

    ans
}
