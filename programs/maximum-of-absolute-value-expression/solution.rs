pub fn max_abs_val_expr(arr1: &[i64], arr2: &[i64]) -> i64 {
    let n = arr1.len();
    let mut best: i64 = 0;

    let mut si = 0;
    while si < 2 {
        let s: i64 = if si == 0 { 1 } else { -1 };

        let mut ti = 0;
        while ti < 2 {
            let t: i64 = if ti == 0 { 1 } else { -1 };

            let mut ui = 0;
            while ui < 2 {
                let u: i64 = if ui == 0 { 1 } else { -1 };

                let first = s * arr1[0] + t * arr2[0] + u * 0;
                let mut mx = first;
                let mut mn = first;

                let mut i = 1;
                while i < n {
                    let ii = i as i64;
                    let val = s * arr1[i] + t * arr2[i] + u * ii;

                    if val > mx {
                        mx = val;
                    }
                    if val < mn {
                        mn = val;
                    }

                    i += 1;
                }

                let diff = mx - mn;
                if diff > best {
                    best = diff;
                }

                ui += 1;
            }

            ti += 1;
        }

        si += 1;
    }

    best
}
