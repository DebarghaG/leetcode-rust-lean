pub fn queens_attackthe_king(queens: &[Vec<i64>], king: &[i64]) -> Vec<Vec<i64>> {
    let kx: i64 = king[0];
    let ky: i64 = king[1];

    let mut attack: Vec<bool> = Vec::new();
    let mut i: i64 = 0;
    while i < 64 {
        attack.push(false);
        i += 1;
    }

    let mut dx: i64 = -1;
    while dx <= 1 {
        let mut dy: i64 = -1;
        while dy <= 1 {
            if !(dx == 0 && dy == 0) {
                let mut step: i64 = 1;
                let mut hit: bool = false;

                while step <= 7 && !hit {
                    let x: i64 = kx + dx * step;
                    let y: i64 = ky + dy * step;

                    if x >= 0 && x < 8 && y >= 0 && y < 8 {
                        let mut qi: usize = 0;
                        while qi < queens.len() && !hit {
                            if queens[qi][0] == x && queens[qi][1] == y {
                                attack[(x * 8 + y) as usize] = true;
                                hit = true;
                            }
                            qi += 1;
                        }
                    }

                    step += 1;
                }
            }
            dy += 1;
        }
        dx += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut x: i64 = 0;
    while x < 8 {
        let mut y: i64 = 0;
        while y < 8 {
            if attack[(x * 8 + y) as usize] {
                let mut q: Vec<i64> = Vec::new();
                q.push(x);
                q.push(y);
                out.push(q);
            }
            y += 1;
        }
        x += 1;
    }

    out
}
