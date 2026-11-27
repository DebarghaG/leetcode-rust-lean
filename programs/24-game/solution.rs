fn apply(an: i64, ad: i64, bn: i64, bd: i64, op: i64) -> Vec<i64> {
    let mut res: Vec<i64> = Vec::new();
    if op == 0 {
        res.push(an * bd + bn * ad);
        res.push(ad * bd);
    } else if op == 1 {
        res.push(an * bd - bn * ad);
        res.push(ad * bd);
    } else if op == 2 {
        res.push(an * bn);
        res.push(ad * bd);
    } else {
        if bn != 0 {
            res.push(an * bd);
            res.push(ad * bn);
        }
    }
    res
}

// (((a op1 b) op2 c) op3 d)
fn shape0(a: i64, b: i64, c: i64, d: i64, op1: i64, op2: i64, op3: i64) -> bool {
    let mut ok = false;
    let r1 = apply(a, 1, b, 1, op1);
    if r1.len() == 2 {
        let r2 = apply(r1[0], r1[1], c, 1, op2);
        if r2.len() == 2 {
            let r3 = apply(r2[0], r2[1], d, 1, op3);
            if r3.len() == 2 && r3[1] != 0 && r3[0] == 24 * r3[1] {
                ok = true;
            }
        }
    }
    ok
}

// ((a op1 (b op2 c)) op3 d)
fn shape1(a: i64, b: i64, c: i64, d: i64, op1: i64, op2: i64, op3: i64) -> bool {
    let mut ok = false;
    let r1 = apply(b, 1, c, 1, op2);
    if r1.len() == 2 {
        let r2 = apply(a, 1, r1[0], r1[1], op1);
        if r2.len() == 2 {
            let r3 = apply(r2[0], r2[1], d, 1, op3);
            if r3.len() == 2 && r3[1] != 0 && r3[0] == 24 * r3[1] {
                ok = true;
            }
        }
    }
    ok
}

// (a op1 b) op2 (c op3 d)
fn shape2(a: i64, b: i64, c: i64, d: i64, op1: i64, op2: i64, op3: i64) -> bool {
    let mut ok = false;
    let r1 = apply(a, 1, b, 1, op1);
    let r2 = apply(c, 1, d, 1, op3);
    if r1.len() == 2 && r2.len() == 2 {
        let r3 = apply(r1[0], r1[1], r2[0], r2[1], op2);
        if r3.len() == 2 && r3[1] != 0 && r3[0] == 24 * r3[1] {
            ok = true;
        }
    }
    ok
}

// a op1 ((b op2 c) op3 d)
fn shape3(a: i64, b: i64, c: i64, d: i64, op1: i64, op2: i64, op3: i64) -> bool {
    let mut ok = false;
    let r1 = apply(b, 1, c, 1, op2);
    if r1.len() == 2 {
        let r2 = apply(r1[0], r1[1], d, 1, op3);
        if r2.len() == 2 {
            let r3 = apply(a, 1, r2[0], r2[1], op1);
            if r3.len() == 2 && r3[1] != 0 && r3[0] == 24 * r3[1] {
                ok = true;
            }
        }
    }
    ok
}

// a op1 (b op2 (c op3 d))
fn shape4(a: i64, b: i64, c: i64, d: i64, op1: i64, op2: i64, op3: i64) -> bool {
    let mut ok = false;
    let r1 = apply(c, 1, d, 1, op3);
    if r1.len() == 2 {
        let r2 = apply(b, 1, r1[0], r1[1], op2);
        if r2.len() == 2 {
            let r3 = apply(a, 1, r2[0], r2[1], op1);
            if r3.len() == 2 && r3[1] != 0 && r3[0] == 24 * r3[1] {
                ok = true;
            }
        }
    }
    ok
}

fn check_perm(a: i64, b: i64, c: i64, d: i64, op1: i64, op2: i64, op3: i64) -> bool {
    let mut ok = shape0(a, b, c, d, op1, op2, op3);
    if !ok {
        ok = shape1(a, b, c, d, op1, op2, op3);
    }
    if !ok {
        ok = shape2(a, b, c, d, op1, op2, op3);
    }
    if !ok {
        ok = shape3(a, b, c, d, op1, op2, op3);
    }
    if !ok {
        ok = shape4(a, b, c, d, op1, op2, op3);
    }
    ok
}

pub fn judge_point24(cards: &[i64]) -> bool {
    let mut found = false;
    if cards.len() == 4 {
        let a0 = cards[0];
        let a1 = cards[1];
        let a2 = cards[2];
        let a3 = cards[3];

        // All 24 permutations of the four card values.
        let mut p: Vec<i64> = Vec::new();

        p.push(a0); p.push(a1); p.push(a2); p.push(a3);
        p.push(a0); p.push(a1); p.push(a3); p.push(a2);
        p.push(a0); p.push(a2); p.push(a1); p.push(a3);
        p.push(a0); p.push(a2); p.push(a3); p.push(a1);
        p.push(a0); p.push(a3); p.push(a1); p.push(a2);
        p.push(a0); p.push(a3); p.push(a2); p.push(a1);

        p.push(a1); p.push(a0); p.push(a2); p.push(a3);
        p.push(a1); p.push(a0); p.push(a3); p.push(a2);
        p.push(a1); p.push(a2); p.push(a0); p.push(a3);
        p.push(a1); p.push(a2); p.push(a3); p.push(a0);
        p.push(a1); p.push(a3); p.push(a0); p.push(a2);
        p.push(a1); p.push(a3); p.push(a2); p.push(a0);

        p.push(a2); p.push(a0); p.push(a1); p.push(a3);
        p.push(a2); p.push(a0); p.push(a3); p.push(a1);
        p.push(a2); p.push(a1); p.push(a0); p.push(a3);
        p.push(a2); p.push(a1); p.push(a3); p.push(a0);
        p.push(a2); p.push(a3); p.push(a0); p.push(a1);
        p.push(a2); p.push(a3); p.push(a1); p.push(a0);

        p.push(a3); p.push(a0); p.push(a1); p.push(a2);
        p.push(a3); p.push(a0); p.push(a2); p.push(a1);
        p.push(a3); p.push(a1); p.push(a0); p.push(a2);
        p.push(a3); p.push(a1); p.push(a2); p.push(a0);
        p.push(a3); p.push(a2); p.push(a0); p.push(a1);
        p.push(a3); p.push(a2); p.push(a1); p.push(a0);

        let nperm = p.len() / 4;
        let mut pi = 0;
        while pi < nperm && !found {
            let base = pi * 4;
            let a = p[base];
            let b = p[base + 1];
            let c = p[base + 2];
            let d = p[base + 3];

            let mut op1: i64 = 0;
            while op1 < 4 && !found {
                let mut op2: i64 = 0;
                while op2 < 4 && !found {
                    let mut op3: i64 = 0;
                    while op3 < 4 && !found {
                        if check_perm(a, b, c, d, op1, op2, op3) {
                            found = true;
                        }
                        op3 += 1;
                    }
                    op2 += 1;
                }
                op1 += 1;
            }
            pi += 1;
        }
    }
    found
}
