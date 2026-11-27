pub fn count_unguarded(m: i64, n: i64, guards: &[Vec<i64>], walls: &[Vec<i64>]) -> i64 {
    let rows = m as usize;
    let cols = n as usize;
    let total = rows * cols;

    let mut grid: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        grid.push(0);
        i += 1;
    }

    // 2 = wall
    let mut wi: usize = 0;
    while wi < walls.len() {
        let r = walls[wi][0] as usize;
        let c = walls[wi][1] as usize;
        grid[r * cols + c] = 2;
        wi += 1;
    }

    // 1 = guard
    let mut gi: usize = 0;
    while gi < guards.len() {
        let r = guards[gi][0] as usize;
        let c = guards[gi][1] as usize;
        grid[r * cols + c] = 1;
        gi += 1;
    }

    // 3 = guarded
    gi = 0;
    while gi < guards.len() {
        let gr = guards[gi][0] as usize;
        let gc = guards[gi][1] as usize;

        // North
        let mut r = gr;
        let c = gc;
        while r > 0 {
            r -= 1;
            let idx = r * cols + c;
            let v = grid[idx];
            if v == 2 || v == 1 {
                break;
            }
            if v == 0 {
                grid[idx] = 3;
            }
        }

        // South
        r = gr;
        while r + 1 < rows {
            r += 1;
            let idx = r * cols + c;
            let v = grid[idx];
            if v == 2 || v == 1 {
                break;
            }
            if v == 0 {
                grid[idx] = 3;
            }
        }

        // West
        r = gr;
        let mut c2 = gc;
        while c2 > 0 {
            c2 -= 1;
            let idx = r * cols + c2;
            let v = grid[idx];
            if v == 2 || v == 1 {
                break;
            }
            if v == 0 {
                grid[idx] = 3;
            }
        }

        // East
        c2 = gc;
        while c2 + 1 < cols {
            c2 += 1;
            let idx = r * cols + c2;
            let v = grid[idx];
            if v == 2 || v == 1 {
                break;
            }
            if v == 0 {
                grid[idx] = 3;
            }
        }

        gi += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < total {
        if grid[i] == 0 {
            ans += 1;
        }
        i += 1;
    }

    ans
}
