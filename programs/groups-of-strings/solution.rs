fn dsu_find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut r = x;
    while parent[r as usize] != r {
        r = parent[r as usize];
    }
    r
}

fn dsu_union(parent: &mut Vec<i64>, weight: &mut Vec<i64>, a: i64, b: i64) {
    let mut ra = dsu_find(parent, a);
    let mut rb = dsu_find(parent, b);

    if ra == rb {
        return;
    }

    if weight[ra as usize] < weight[rb as usize] {
        let tmp = ra;
        ra = rb;
        rb = tmp;
    }

    parent[rb as usize] = ra;
    weight[ra as usize] = weight[ra as usize] + weight[rb as usize];
}

pub fn group_strings(words: &[Vec<u8>]) -> Vec<i64> {
    let n = words.len();

    let mut cap: usize = 1;
    while cap < 2 * n + 1 {
        cap = cap * 2;
    }
    let cap_i = cap as i64;

    let mut keys: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < cap {
        keys.push(-1);
        vals.push(0);
        t += 1;
    }

    let mut masks: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut wi: usize = 0;
    while wi < n {
        let w = &words[wi];
        let mut mask: i64 = 0;

        let mut cj: usize = 0;
        while cj < w.len() {
            let pos: usize = (w[cj] - b'a') as usize;
            mask = mask | (1i64 << pos);
            cj += 1;
        }

        let mut idx: usize = (((mask * 2654435761i64) & (cap_i - 1)) as usize);
        while keys[idx] != -1 && keys[idx] != mask {
            idx = (idx + 1) & (cap - 1);
        }

        if keys[idx] == -1 {
            let id = masks.len() as i64;
            keys[idx] = mask;
            vals[idx] = id;
            masks.push(mask);
            counts.push(1);
        } else {
            let id = vals[idx] as usize;
            counts[id] = counts[id] + 1;
        }

        wi += 1;
    }

    let m = masks.len();

    let mut parent: Vec<i64> = Vec::new();
    let mut weight: Vec<i64> = Vec::new();
    let mut pi: usize = 0;
    while pi < m {
        parent.push(pi as i64);
        weight.push(counts[pi]);
        pi += 1;
    }

    let mut total_dels: usize = 0;
    let mut mi: usize = 0;
    while mi < m {
        let mask = masks[mi];

        let mut b: usize = 0;
        while b < 26 {
            let bit: i64 = 1i64 << b;
            if (mask & bit) != 0 {
                total_dels += 1;
            }
            b += 1;
        }

        mi += 1;
    }

    let mut dcap: usize = 1;
    while dcap < 2 * total_dels + 1 {
        dcap = dcap * 2;
    }
    let dcap_i = dcap as i64;

    let mut dkeys: Vec<i64> = Vec::new();
    let mut dvals: Vec<i64> = Vec::new();
    let mut di: usize = 0;
    while di < dcap {
        dkeys.push(-1);
        dvals.push(0);
        di += 1;
    }

    mi = 0;
    while mi < m {
        let mask = masks[mi];

        let mut b: usize = 0;
        while b < 26 {
            let bit: i64 = 1i64 << b;

            if (mask & bit) != 0 {
                let del = mask ^ bit;

                let mut idx: usize = (((del * 2654435761i64) & (cap_i - 1)) as usize);
                while keys[idx] != -1 && keys[idx] != del {
                    idx = (idx + 1) & (cap - 1);
                }

                if keys[idx] == del {
                    let j = vals[idx];
                    dsu_union(&mut parent, &mut weight, mi as i64, j);
                }

                let mut didx: usize = (((del * 2654435761i64) & (dcap_i - 1)) as usize);
                while dkeys[didx] != -1 && dkeys[didx] != del {
                    didx = (didx + 1) & (dcap - 1);
                }

                if dkeys[didx] == -1 {
                    dkeys[didx] = del;
                    dvals[didx] = mi as i64;
                } else {
                    let rep = dvals[didx];
                    dsu_union(&mut parent, &mut weight, mi as i64, rep);
                }
            }

            b += 1;
        }

        mi += 1;
    }

    let mut groups: i64 = 0;
    let mut largest: i64 = 0;

    let mut i: usize = 0;
    while i < m {
        if parent[i] == i as i64 {
            groups += 1;
            let sz = weight[i];
            if sz > largest {
                largest = sz;
            }
        }
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    ans.push(groups);
    ans.push(largest);
    ans
}
