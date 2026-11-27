pub fn high_five(items: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = items.len();
    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut last_id: i64 = 0;
    let mut going: bool = true;

    while going {
        let mut next_id: i64 = 0;
        let mut k: usize = 0;

        while k < n {
            let id = items[k][0];
            if id > last_id {
                if next_id == 0 || id < next_id {
                    next_id = id;
                }
            }
            k += 1;
        }

        if next_id == 0 {
            going = false;
        } else {
            let mut t0: i64 = 0;
            let mut t1: i64 = 0;
            let mut t2: i64 = 0;
            let mut t3: i64 = 0;
            let mut t4: i64 = 0;

            let mut j: usize = 0;
            while j < n {
                if items[j][0] == next_id {
                    let score = items[j][1];

                    if score > t0 {
                        t4 = t3;
                        t3 = t2;
                        t2 = t1;
                        t1 = t0;
                        t0 = score;
                    } else if score > t1 {
                        t4 = t3;
                        t3 = t2;
                        t2 = t1;
                        t1 = score;
                    } else if score > t2 {
                        t4 = t3;
                        t3 = t2;
                        t2 = score;
                    } else if score > t3 {
                        t4 = t3;
                        t3 = score;
                    } else if score > t4 {
                        t4 = score;
                    }
                }
                j += 1;
            }

            let avg = (t0 + t1 + t2 + t3 + t4) / 5;

            let mut pair: Vec<i64> = Vec::new();
            pair.push(next_id);
            pair.push(avg);
            out.push(pair);

            last_id = next_id;
        }
    }

    out
}
