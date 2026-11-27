pub fn rectangle_area(rectangles: &[Vec<i64>]) -> i64 {
    let n = rectangles.len();

    let mut xs: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let r = &rectangles[i];
        xs.push(r[0]);
        xs.push(r[2]);
        i += 1;
    }

    let mut a = 1usize;
    while a < xs.len() {
        let key = xs[a];
        let mut b = a;
        while b > 0 && xs[b - 1] > key {
            xs[b] = xs[b - 1];
            b -= 1;
        }
        xs[b] = key;
        a += 1;
    }

    let mut ux: Vec<i64> = Vec::new();
    if xs.len() > 0 {
        ux.push(xs[0]);
    }
    let mut c = 1usize;
    while c < xs.len() {
        if xs[c] != xs[c - 1] {
            ux.push(xs[c]);
        }
        c += 1;
    }

    let modulus: i64 = 1000000007;
    let mut total: i64 = 0;
    let mut xi = 0usize;
    while xi + 1 < ux.len() {
        let x_left = ux[xi];
        let x_right = ux[xi + 1];
        let width = x_right - x_left;

        let mut lows: Vec<i64> = Vec::new();
        let mut highs: Vec<i64> = Vec::new();
        let mut rk = 0usize;
        while rk < n {
            let r = &rectangles[rk];
            if r[0] <= x_left && x_right <= r[2] {
                lows.push(r[1]);
                highs.push(r[3]);
            }
            rk += 1;
        }

        let len = lows.len();
        let mut p = 1usize;
        while p < len {
            let key_low = lows[p];
            let key_high = highs[p];
            let mut q = p;
            while q > 0 && lows[q - 1] > key_low {
                lows[q] = lows[q - 1];
                highs[q] = highs[q - 1];
                q -= 1;
            }
            lows[q] = key_low;
            highs[q] = key_high;
            p += 1;
        }

        let mut union_len: i64 = 0;
        if len > 0 {
            let mut cur_low = lows[0];
            let mut cur_high = highs[0];
            let mut idx = 1usize;
            while idx < len {
                let l = lows[idx];
                let h = highs[idx];
                if l <= cur_high {
                    if h > cur_high {
                        cur_high = h;
                    }
                } else {
                    union_len += cur_high - cur_low;
                    cur_low = l;
                    cur_high = h;
                }
                idx += 1;
            }
            union_len += cur_high - cur_low;
        }

        let area = ((width % modulus) * (union_len % modulus)) % modulus;
        total = (total + area) % modulus;
        xi += 1;
    }

    total
}
