pub fn num_equiv_domino_pairs(dominoes: &[Vec<i64>]) -> i64 {
    let n = dominoes.len();
    if n == 0 {
        return 0;
    }

    let mut table_size: usize = 1;
    while table_size < n * 2 {
        table_size *= 2;
    }

    let mut used: Vec<bool> = Vec::new();
    let mut key_lo: Vec<i64> = Vec::new();
    let mut key_hi: Vec<i64> = Vec::new();
    let mut count: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < table_size {
        used.push(false);
        key_lo.push(0);
        key_hi.push(0);
        count.push(0);
        i += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < n {
        let a = dominoes[i][0];
        let b = dominoes[i][1];

        let lo: i64;
        let hi: i64;
        if a < b {
            lo = a;
            hi = b;
        } else {
            lo = b;
            hi = a;
        }

        let m = table_size as i64;
        let x0 = lo % m;
        let x = if x0 < 0 { x0 + m } else { x0 };
        let y0 = hi % m;
        let y = if y0 < 0 { y0 + m } else { y0 };
        let h0 = (x * 31 + y) % m;
        let h = if h0 < 0 { h0 + m } else { h0 };

        let mut pos: usize = h as usize;
        let mut done: bool = false;
        while !done {
            if !used[pos] {
                used[pos] = true;
                key_lo[pos] = lo;
                key_hi[pos] = hi;
                count[pos] = 1;
                done = true;
            } else if key_lo[pos] == lo && key_hi[pos] == hi {
                ans += count[pos];
                count[pos] = count[pos] + 1;
                done = true;
            } else {
                pos = (pos + 1) % table_size;
            }
        }

        i += 1;
    }

    ans
}
