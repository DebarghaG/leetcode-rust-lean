fn bit_value(pos: i64) -> i64 {
    let mut result: i64 = 1;
    let mut i: i64 = 0;
    while i < pos {
        result = result * 2;
        i += 1;
    }
    result
}

pub fn min_number_of_semesters(n: i64, relations: &[Vec<i64>], k: i64) -> i64 {
    let mut prereq: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n {
        prereq.push(0);
        i += 1;
    }

    let mut r: usize = 0;
    while r < relations.len() {
        let prev: i64 = relations[r][0] - 1;
        let next: i64 = relations[r][1] - 1;
        let bit: i64 = bit_value(prev);
        let idx: usize = next as usize;
        prereq[idx] = prereq[idx] | bit;
        r += 1;
    }

    let total: i64 = bit_value(n);
    let allmask: i64 = total - 1;

    let mut pop: Vec<i64> = Vec::new();
    pop.push(0);
    let mut v: i64 = 1;
    while v < total {
        let half: i64 = v / 2;
        let add: i64 = v % 2;
        let prev_count: i64 = pop[half as usize];
        pop.push(prev_count + add);
        v += 1;
    }

    let inf: i64 = 1000000000;
    let mut dp: Vec<i64> = Vec::new();
    let mut d: i64 = 0;
    while d < total {
        dp.push(inf);
        d += 1;
    }
    dp[0] = 0;

    let mut mask: i64 = 0;
    while mask < total {
        if dp[mask as usize] != inf {
            let not_taken: i64 = allmask ^ mask;
            let mut avail: i64 = 0;
            let mut bit: i64 = 1;
            let mut c: i64 = 0;

            while c < n {
                let pre: i64 = prereq[c as usize];
                if (mask & pre) == pre && (not_taken & bit) != 0 {
                    avail = avail | bit;
                }
                bit = bit * 2;
                c += 1;
            }

            if avail != 0 {
                let cnt: i64 = pop[avail as usize];
                if cnt <= k {
                    let newmask: i64 = mask | avail;
                    let val: i64 = dp[mask as usize] + 1;
                    if val < dp[newmask as usize] {
                        dp[newmask as usize] = val;
                    }
                } else {
                    let mut sub: i64 = avail;
                    while sub > 0 {
                        if pop[sub as usize] == k {
                            let newmask: i64 = mask | sub;
                            let val: i64 = dp[mask as usize] + 1;
                            if val < dp[newmask as usize] {
                                dp[newmask as usize] = val;
                            }
                        }
                        sub = (sub - 1) & avail;
                    }
                }
            }
        }
        mask += 1;
    }

    dp[allmask as usize]
}
