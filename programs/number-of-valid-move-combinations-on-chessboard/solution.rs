fn gen_moves(kind: u8, r: i64, c: i64) -> Vec<i64> {
    let mut m: Vec<i64> = Vec::new();
    // Stay-in-place move: dr = 0, dc = 0, dist = 0
    m.push(0i64);
    m.push(0i64);
    m.push(0i64);

    let mut di = 0i64;
    while di < 3 {
        let dr = di - 1;
        let mut dci = 0i64;
        while dci < 3 {
            let dc = dci - 1;

            let mut ok = true;
            if dr == 0 && dc == 0 {
                ok = false;
            }
            if kind == b'r' && dr != 0 && dc != 0 {
                ok = false;
            }
            if kind == b'b' && (dr == 0 || dc == 0) {
                ok = false;
            }

            if ok {
                // Largest step count staying on the board in direction (dr, dc).
                let mut maxk = 7i64;
                if dr == 1 && 7 - r < maxk {
                    maxk = 7 - r;
                }
                if dr == -1 && r < maxk {
                    maxk = r;
                }
                if dc == 1 && 7 - c < maxk {
                    maxk = 7 - c;
                }
                if dc == -1 && c < maxk {
                    maxk = c;
                }

                let mut k = 1i64;
                while k <= maxk {
                    m.push(dr);
                    m.push(dc);
                    m.push(k);
                    k += 1;
                }
            }

            dci += 1;
        }
        di += 1;
    }

    m
}

fn valid_combo(choice: &[usize], moves: &[Vec<i64>], positions: &[Vec<i64>]) -> bool {
    let n = choice.len();
    let mut valid = true;
    let mut t = 0i64;
    while t < 8 && valid {
        let mut a = 0usize;
        while a < n && valid {
            let ma = choice[a];
            let dra = moves[a][ma * 3];
            let dca = moves[a][ma * 3 + 1];
            let dista = moves[a][ma * 3 + 2];

            let mut ta = t;
            if ta > dista {
                ta = dista;
            }
            let ra = positions[a][0] - 1 + dra * ta;
            let ca = positions[a][1] - 1 + dca * ta;

            let mut b = a + 1;
            while b < n && valid {
                let mb = choice[b];
                let drb = moves[b][mb * 3];
                let dcb = moves[b][mb * 3 + 1];
                let distb = moves[b][mb * 3 + 2];

                let mut tb = t;
                if tb > distb {
                    tb = distb;
                }
                let rb = positions[b][0] - 1 + drb * tb;
                let cb = positions[b][1] - 1 + dcb * tb;

                if ra == rb && ca == cb {
                    valid = false;
                }
                b += 1;
            }

            a += 1;
        }
        t += 1;
    }
    valid
}

pub fn count_combinations(pieces: &[Vec<u8>], positions: &[Vec<i64>]) -> i64 {
    let n = pieces.len();
    if n == 0 {
        return 0;
    }

    // One flat move list per piece: triples (dr, dc, dist).
    let mut all_moves: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let ms = gen_moves(pieces[i][0], positions[i][0] - 1, positions[i][1] - 1);
        all_moves.push(ms);
        i += 1;
    }

    // Total number of combinations.
    let mut num_combos: usize = 1;
    i = 0;
    while i < n {
        num_combos = num_combos * (all_moves[i].len() / 3);
        i += 1;
    }

    let mut choice: Vec<usize> = Vec::new();
    i = 0;
    while i < n {
        choice.push(0usize);
        i += 1;
    }

    let mut total: i64 = 0;
    let mut idx: usize = 0;
    while idx < num_combos {
        // Mixed-radix decode of idx into per-piece move indices.
        let mut rem = idx;
        i = 0;
        while i < n {
            let mc = all_moves[i].len() / 3;
            choice[i] = rem % mc;
            rem = rem / mc;
            i += 1;
        }

        if valid_combo(&choice, &all_moves, positions) {
            total += 1;
        }

        idx += 1;
    }

    total
}
