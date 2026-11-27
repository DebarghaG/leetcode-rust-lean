pub fn count_substrings(s: &[u8]) -> i64 {
    let mut old: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 100 {
        old.push(0);
        i += 1;
    }

    let mut new: Vec<i64> = Vec::new();
    i = 0;
    while i < 100 {
        new.push(0);
        i += 1;
    }

    let mut ans: i64 = 0;
    let n: usize = s.len();
    i = 0;

    while i < n {
        let x: usize = (s[i] as usize) - 48;

        let mut k: usize = 0;
        while k < 100 {
            new[k] = 0;
            k += 1;
        }

        let mut d: usize = 1;
        while d <= 9 {
            let base: usize = d * 10;

            let mut r: usize = 0;
            while r < d {
                let c: i64 = old[base + r];
                if c > 0 {
                    let nr: usize = (r * 10 + x) % d;
                    new[base + nr] = new[base + nr] + c;
                }
                r += 1;
            }

            let rem: usize = x % d;
            new[base + rem] = new[base + rem] + 1;

            d += 1;
        }

        if x != 0 {
            ans = ans + new[x * 10];
        }

        let mut p: usize = 0;
        while p < 100 {
            old[p] = new[p];
            p += 1;
        }

        i += 1;
    }

    ans
}
