pub fn count_sub_islands(grid1: &[Vec<i64>], grid2: &[Vec<i64>]) -> i64 {
    let m = grid1.len();
    if m == 0 {
        return 0;
    }
    let n = grid1[0].len();
    if n == 0 {
        return 0;
    }

    let mut visited: Vec<Vec<bool>> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        let mut row: Vec<bool> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            row.push(false);
            j += 1;
        }
        visited.push(row);
        i += 1;
    }

    let total = m * n;
    let mut stack: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < total {
        stack.push(0);
        k += 1;
    }

    let mut count: i64 = 0;
    let mut r: usize = 0;
    while r < m {
        let mut c: usize = 0;
        while c < n {
            if grid2[r][c] == 1 && !visited[r][c] {
                let mut is_sub = true;
                let mut sp: usize = 0;
                stack[sp] = r * n + c;
                sp += 1;
                visited[r][c] = true;

                while sp > 0 {
                    sp -= 1;
                    let idx = stack[sp];
                    let ci = idx / n;
                    let cj = idx % n;

                    if grid1[ci][cj] != 1 {
                        is_sub = false;
                    }

                    if ci > 0 {
                        let ni = ci - 1;
                        let nj = cj;
                        if grid2[ni][nj] == 1 && !visited[ni][nj] {
                            visited[ni][nj] = true;
                            stack[sp] = ni * n + nj;
                            sp += 1;
                        }
                    }
                    if ci + 1 < m {
                        let ni = ci + 1;
                        let nj = cj;
                        if grid2[ni][nj] == 1 && !visited[ni][nj] {
                            visited[ni][nj] = true;
                            stack[sp] = ni * n + nj;
                            sp += 1;
                        }
                    }
                    if cj > 0 {
                        let ni = ci;
                        let nj = cj - 1;
                        if grid2[ni][nj] == 1 && !visited[ni][nj] {
                            visited[ni][nj] = true;
                            stack[sp] = ni * n + nj;
                            sp += 1;
                        }
                    }
                    if cj + 1 < n {
                        let ni = ci;
                        let nj = cj + 1;
                        if grid2[ni][nj] == 1 && !visited[ni][nj] {
                            visited[ni][nj] = true;
                            stack[sp] = ni * n + nj;
                            sp += 1;
                        }
                    }
                }

                if is_sub {
                    count += 1;
                }
            }
            c += 1;
        }
        r += 1;
    }

    count
}
