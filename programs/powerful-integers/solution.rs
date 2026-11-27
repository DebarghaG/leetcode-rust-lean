pub fn powerful_integers(x: i64, y: i64, bound: i64) -> Vec<i64> {
    let mut sums: Vec<i64> = Vec::new();

    let mut xi: i64 = 1;
    let mut stop_x: bool = false;
    while !stop_x {
        if xi > bound {
            stop_x = true;
        } else {
            let mut yj: i64 = 1;
            let mut stop_y: bool = false;
            while !stop_y {
                let s = xi + yj;
                if s > bound {
                    stop_y = true;
                } else {
                    sums.push(s);
                    if y == 1 {
                        stop_y = true;
                    } else {
                        yj = yj * y;
                    }
                }
            }

            if x == 1 {
                stop_x = true;
            } else {
                xi = xi * x;
            }
        }
    }

    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < sums.len() {
        let v = sums[i];
        let mut duplicate: bool = false;
        let mut j: usize = 0;
        while j < out.len() {
            if out[j] == v {
                duplicate = true;
            }
            j += 1;
        }
        if !duplicate {
            out.push(v);
        }
        i += 1;
    }

    out
}
