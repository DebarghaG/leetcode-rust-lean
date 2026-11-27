fn greedy(mut a: i64, mut b: i64) -> i64 {
    let mut count: i64 = 0;
    while a > 0 {
        if a > b {
            let t = a;
            a = b;
            b = t;
        }
        count += b / a;
        let r = b % a;
        b = a;
        a = r;
    }
    count
}

fn lowest_height(state: i64, width: i64, height: i64) -> i64 {
    let mut mnh: i64 = height;
    let mut c: i64 = 0;
    while c < width {
        let h: i64 = (state >> (4 * c)) & 15;
        if h < mnh {
            mnh = h;
        }
        c += 1;
    }
    mnh
}

// Returns the first column achieving the minimum height.
// Packs (height, column) as height*16 + column so a single accumulator
// both tracks the minimum height and breaks ties by smallest column.
fn lowest_cell(state: i64, width: i64, height: i64) -> i64 {
    let mut best: i64 = height * 16 + 16;
    let mut c: i64 = 0;
    while c < width {
        let h: i64 = (state >> (4 * c)) & 15;
        let v: i64 = h * 16 + c;
        if v < best {
            best = v;
        }
        c += 1;
    }
    best % 16
}

fn max_size_at(state: i64, cell: i64, mnh: i64, width: i64, height: i64) -> i64 {
    let hcap: i64 = height - mnh;
    let mut ms: i64 = 0;
    let mut scanning: bool = true;
    while scanning {
        if ms >= hcap {
            scanning = false;
        } else {
            let col: i64 = cell + ms;
            if col >= width {
                scanning = false;
            } else {
                let h: i64 = (state >> (4 * col)) & 15;
                if h == mnh {
                    ms += 1;
                } else {
                    scanning = false;
                }
            }
        }
    }
    ms
}

fn place(state: i64, cell: i64, mh: i64, s: i64) -> i64 {
    let mut st: i64 = state;
    let mut j: i64 = cell;
    while j < cell + s {
        let sh: i64 = 4 * j;
        let old: i64 = (st >> sh) & 15;
        let v: i64 = mh + s;
        st = st ^ ((old ^ v) << sh);
        j += 1;
    }
    st
}

fn can(
    state: i64,
    filled: i64,
    s_limit: i64,
    budget: i64,
    width: i64,
    height: i64,
    area: i64,
    max_sq: i64,
) -> bool {
    let mnh: i64 = lowest_height(state, width, height);
    if mnh == height {
        return true;
    }

    let remaining: i64 = area - filled;
    let min_needed: i64 = (remaining + max_sq - 1) / max_sq;
    if min_needed > budget {
        return false;
    }

    let cell: i64 = lowest_cell(state, width, height);
    let ms: i64 = max_size_at(state, cell, mnh, width, height);

    let mut s: i64 = ms;
    if s_limit < s {
        s = s_limit;
    }
    if s <= 0 {
        return false;
    }
    if budget <= 0 {
        return false;
    }

    let ns: i64 = place(state, cell, mnh, s);
    if can(ns, filled + s * s, width, budget - 1, width, height, area, max_sq) {
        return true;
    }

    if can(state, filled, s - 1, budget, width, height, area, max_sq) {
        return true;
    }

    false
}

fn find(
    bnd: i64,
    upper: i64,
    width: i64,
    height: i64,
    area: i64,
    max_sq: i64,
) -> i64 {
    if bnd > upper {
        return upper;
    }
    if can(0, 0, width, bnd, width, height, area, max_sq) {
        return bnd;
    }
    find(bnd + 1, upper, width, height, area, max_sq)
}

pub fn tiling_rectangle(n: i64, m: i64) -> i64 {
    if n == m {
        return 1;
    }
    let width: i64 = if n < m { n } else { m };
    let height: i64 = if n < m { m } else { n };
    let area: i64 = width * height;
    let max_sq: i64 = width * width;
    let upper: i64 = greedy(width, height);
    find(1, upper, width, height, area, max_sq)
}
