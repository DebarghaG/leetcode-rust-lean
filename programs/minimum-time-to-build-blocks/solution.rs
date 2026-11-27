pub fn min_build_time(blocks: &[i64], split: i64) -> i64 {
    let n0 = blocks.len();
    if n0 == 0 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n0 {
        v.push(blocks[idx]);
        idx += 1;
    }

    while v.len() > 1 {
        let n = v.len();

        let mut i1: usize = 0;
        let mut k: usize = 1;
        while k < n {
            if v[k] < v[i1] {
                i1 = k;
            }
            k += 1;
        }

        let mut i2: usize = 0;
        if i1 == 0 {
            i2 = 1;
        }

        k = 0;
        while k < n {
            if k != i1 {
                if v[k] < v[i2] {
                    i2 = k;
                }
            }
            k += 1;
        }

        let mut mx = v[i1];
        if v[i2] > mx {
            mx = v[i2];
        }
        let z = mx + split;

        let mut nv: Vec<i64> = Vec::new();
        k = 0;
        while k < n {
            if k != i1 {
                if k != i2 {
                    nv.push(v[k]);
                }
            }
            k += 1;
        }
        nv.push(z);
        v = nv;
    }

    v[0]
}
