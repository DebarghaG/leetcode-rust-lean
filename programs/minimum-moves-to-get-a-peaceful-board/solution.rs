pub fn min_moves(rooks: &[Vec<i64>]) -> i64 {
    let n: usize = rooks.len();
    let mut xs: Vec<i64> = Vec::new();
    let mut ys: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        xs.push(rooks[i][0]);
        ys.push(rooks[i][1]);
        i = i + 1;
    }

    sort_i64(&mut xs);
    sort_i64(&mut ys);

    let mut ans: i64 = 0;
    let mut k: usize = 0;
    let mut target: i64 = 0;

    while k < n {
        let dx: i64 = xs[k] - target;
        if dx >= 0 {
            ans = ans + dx;
        } else {
            ans = ans - dx;
        }

        let dy: i64 = ys[k] - target;
        if dy >= 0 {
            ans = ans + dy;
        } else {
            ans = ans - dy;
        }

        k = k + 1;
        target = target + 1;
    }

    ans
}

fn sort_i64(v: &mut Vec<i64>) {
    let n: usize = v.len();
    let mut i: usize = 0;

    while i < n {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;

        while j < n {
            if v[j] < v[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }

        if min_idx != i {
            let tmp: i64 = v[i];
            v[i] = v[min_idx];
            v[min_idx] = tmp;
        }

        i = i + 1;
    }
}
