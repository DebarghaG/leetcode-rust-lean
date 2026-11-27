pub fn minimum_operations_to_make_equal(x: i64, y: i64) -> i64 {
    if x <= y {
        return y - x;
    }

    let mut answer: i64 = x - y;

    let mut cur_v: Vec<i64> = Vec::new();
    let mut cur_c: Vec<i64> = Vec::new();
    cur_v.push(x);
    cur_c.push(0);

    while cur_v.len() > 0 {
        let n: usize = cur_v.len();
        let mut next_v: Vec<i64> = Vec::new();
        let mut next_c: Vec<i64> = Vec::new();

        let mut i: usize = 0;
        while i < n {
            let v: i64 = cur_v[i];
            let c: i64 = cur_c[i];

            // Stop dividing at v and adjust v directly to y.
            let mut stop: i64 = c + (v - y);
            if v < y {
                stop = c + (y - v);
            }
            if stop < answer {
                answer = stop;
            }

            if v > y {
                // Divide by 5 after moving down to the nearest multiple.
                let q5: i64 = v / 5;
                let r5: i64 = v % 5;
                let nc1: i64 = c + r5 + 1;
                if nc1 < answer {
                    next_v.push(q5);
                    next_c.push(nc1);
                }

                // Divide by 5 after moving up to the next multiple.
                if r5 != 0 {
                    let nc2: i64 = c + (5 - r5) + 1;
                    if nc2 < answer {
                        next_v.push(q5 + 1);
                        next_c.push(nc2);
                    }
                }

                // Divide by 11 after moving down to the nearest multiple.
                let q11: i64 = v / 11;
                let r11: i64 = v % 11;
                let nc3: i64 = c + r11 + 1;
                if nc3 < answer {
                    next_v.push(q11);
                    next_c.push(nc3);
                }

                // Divide by 11 after moving up to the next multiple.
                if r11 != 0 {
                    let nc4: i64 = c + (11 - r11) + 1;
                    if nc4 < answer {
                        next_v.push(q11 + 1);
                        next_c.push(nc4);
                    }
                }
            }

            i += 1;
        }

        cur_v = next_v;
        cur_c = next_c;
    }

    answer
}
