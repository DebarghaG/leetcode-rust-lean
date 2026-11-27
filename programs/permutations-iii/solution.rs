pub fn permute(n: i64) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();

    if n <= 0 {
        return out;
    }

    let nn: usize = n as usize;

    let mut cur: Vec<i64> = Vec::new();
    let mut nextv: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < nn {
        cur.push(0);
        nextv.push(1);
        i += 1;
    }

    let mut depth: usize = 0;
    let mut done: bool = false;

    while !done {
        if depth == nn {
            let mut row: Vec<i64> = Vec::new();
            let mut j: usize = 0;
            while j < nn {
                row.push(cur[j]);
                j += 1;
            }
            out.push(row);

            if depth == 0 {
                done = true;
            } else {
                depth -= 1;
            }
            continue;
        }

        let mut v: i64 = nextv[depth];
        let mut step: i64 = 1;

        if depth > 0 {
            let prev: i64 = cur[depth - 1];
            let need: i64 = 1 - (prev % 2);

            if v % 2 != need {
                v += 1;
            }
            step = 2;
        } else {
            if n % 2 == 1 {
                if v % 2 == 0 {
                    v += 1;
                }
                step = 2;
            }
        }

        let mut found: bool = false;

        while v <= n {
            let mut used: bool = false;
            let mut j: usize = 0;

            while j < depth {
                if cur[j] == v {
                    used = true;
                }
                j += 1;
            }

            if !used {
                cur[depth] = v;
                nextv[depth] = v + step;
                depth += 1;

                if depth < nn {
                    nextv[depth] = 1;
                }

                found = true;
                break;
            }

            v += step;
        }

        if !found {
            if depth == 0 {
                done = true;
            } else {
                depth -= 1;
            }
        }
    }

    out
}
