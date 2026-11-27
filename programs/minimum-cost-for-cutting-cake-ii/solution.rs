fn sort_asc(mut a: Vec<i64>) -> Vec<i64> {
    let n = a.len();
    if n <= 1 {
        return a;
    }

    let mut b: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        b.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut l: usize = 0;
        while l < n {
            let mid: usize = if l + width < n { l + width } else { n };
            let r: usize = if l + width + width < n {
                l + width + width
            } else {
                n
            };

            let mut i: usize = l;
            let mut j: usize = mid;
            let mut k: usize = l;

            while i < mid && j < r {
                if a[i] <= a[j] {
                    b[k] = a[i];
                    i += 1;
                } else {
                    b[k] = a[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                b[k] = a[i];
                i += 1;
                k += 1;
            }

            while j < r {
                b[k] = a[j];
                j += 1;
                k += 1;
            }

            l = r;
        }

        let mut x: usize = 0;
        while x < n {
            a[x] = b[x];
            x += 1;
        }

        width = width + width;
    }

    a
}

pub fn minimum_cost(
    m: i64,
    n: i64,
    horizontalCut: &[i64],
    verticalCut: &[i64],
) -> i64 {
    let mut h: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < horizontalCut.len() {
        h.push(horizontalCut[i]);
        i += 1;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < verticalCut.len() {
        v.push(verticalCut[j]);
        j += 1;
    }

    h = sort_asc(h);
    v = sort_asc(v);

    // Number of horizontal / vertical cuts implied by the grid dimensions.
    let mut want_h: i64 = m - 1;
    if want_h < 0 {
        want_h = 0;
    }
    let mut want_v: i64 = n - 1;
    if want_v < 0 {
        want_v = 0;
    }

    // Keep only the (up to) "want_h" / "want_v" most expensive cuts.
    // Since arrays are sorted ascending, these are the suffixes.
    let mut cnt_h: usize = h.len();
    if want_h < h.len() as i64 {
        cnt_h = want_h as usize;
    }
    let mut cnt_v: usize = v.len();
    if want_v < v.len() as i64 {
        cnt_v = want_v as usize;
    }

    let mut hh: Vec<i64> = Vec::new();
    let start_h: usize = h.len() - cnt_h;
    let mut a: usize = start_h;
    while a < h.len() {
        hh.push(h[a]);
        a += 1;
    }

    let mut vv: Vec<i64> = Vec::new();
    let start_v: usize = v.len() - cnt_v;
    let mut b: usize = start_v;
    while b < v.len() {
        vv.push(v[b]);
        b += 1;
    }

    let mut hp: usize = hh.len();
    let mut vp: usize = vv.len();
    let mut horizontal_cuts: i64 = 0;
    let mut vertical_cuts: i64 = 0;
    let mut total: i64 = 0;

    while hp > 0 && vp > 0 {
        if hh[hp - 1] > vv[vp - 1] {
            total += hh[hp - 1] * (vertical_cuts + 1);
            hp -= 1;
            horizontal_cuts += 1;
        } else {
            total += vv[vp - 1] * (horizontal_cuts + 1);
            vp -= 1;
            vertical_cuts += 1;
        }
    }

    while hp > 0 {
        total += hh[hp - 1] * (vertical_cuts + 1);
        hp -= 1;
        horizontal_cuts += 1;
    }

    while vp > 0 {
        total += vv[vp - 1] * (horizontal_cuts + 1);
        vp -= 1;
        vertical_cuts += 1;
    }

    total
}
