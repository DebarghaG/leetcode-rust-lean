pub fn combine(n: i64, k: i64) -> Vec<Vec<i64>> {
    let mut res: Vec<Vec<i64>> = Vec::new();

    if k <= 0 || k > n {
        return res;
    }

    let ku: usize = k as usize;

    let mut cur: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < ku {
        cur.push((i as i64) + 1);
        i += 1;
    }

    let mut first: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < ku {
        first.push(cur[t]);
        t += 1;
    }
    res.push(first);

    let mut done: bool = false;
    while !done {
        let mut pivot: usize = ku;
        let mut p: usize = ku;

        while p > 0 {
            p -= 1;
            let max_value: i64 = n - k + 1 + (p as i64);
            if cur[p] < max_value {
                pivot = p;
                p = 0;
            }
        }

        if pivot == ku {
            done = true;
        } else {
            cur[pivot] = cur[pivot] + 1;

            let mut j: usize = pivot + 1;
            while j < ku {
                cur[j] = cur[j - 1] + 1;
                j += 1;
            }

            let mut next_row: Vec<i64> = Vec::new();
            let mut q: usize = 0;
            while q < ku {
                next_row.push(cur[q]);
                q += 1;
            }
            res.push(next_row);
        }
    }

    res
}
