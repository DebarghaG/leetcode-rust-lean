pub fn min_days(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let mut memo: Vec<i64> = Vec::new();

    let mut st_n: Vec<i64> = Vec::new();
    let mut st_stage: Vec<i64> = Vec::new();
    let mut st_a: Vec<i64> = Vec::new();

    st_n.push(n);
    st_stage.push(0);
    st_a.push(0);

    let mut sp: usize = 1;
    let mut last: i64 = 0;
    let mut have_result: bool = false;

    while sp > 0 {
        let top: usize = sp - 1;
        let cur: i64 = st_n[top];
        let stage: i64 = st_stage[top];

        if have_result {
            if stage == 1 {
                let a: i64 = last + (cur % 2);
                st_a[top] = a;
                st_stage[top] = 2;
                have_result = false;
            } else {
                let b: i64 = last + (cur % 3);
                let a: i64 = st_a[top];

                let mut best: i64 = a;
                if b < best {
                    best = b;
                }

                let res: i64 = best + 1;

                memo.push(cur);
                memo.push(res);

                sp -= 1;
                last = res;
                have_result = true;
            }
            continue;
        }

        if stage == 0 {
            if cur <= 1 {
                sp -= 1;
                last = cur;
                have_result = true;
            } else {
                let mut idx: usize = 0;
                let mut found: bool = false;
                let mut val: i64 = 0;

                while idx + 1 < memo.len() {
                    if found == false {
                        if memo[idx] == cur {
                            found = true;
                            val = memo[idx + 1];
                        }
                    }
                    idx += 2;
                }

                if found {
                    sp -= 1;
                    last = val;
                    have_result = true;
                } else {
                    st_stage[top] = 1;

                    let child: i64 = cur / 2;
                    if sp == st_n.len() {
                        st_n.push(child);
                        st_stage.push(0);
                        st_a.push(0);
                    } else {
                        st_n[sp] = child;
                        st_stage[sp] = 0;
                        st_a[sp] = 0;
                    }
                    sp += 1;
                }
            }
        } else if stage == 2 {
            let child: i64 = cur / 3;
            if sp == st_n.len() {
                st_n.push(child);
                st_stage.push(0);
                st_a.push(0);
            } else {
                st_n[sp] = child;
                st_stage[sp] = 0;
                st_a[sp] = 0;
            }
            sp += 1;
        }
    }

    last
}
