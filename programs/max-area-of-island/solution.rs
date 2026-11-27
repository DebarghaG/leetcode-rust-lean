pub fn max_area_of_island(grid: &[Vec<i64>]) -> i64 {
    let m: usize = grid.len();
    if m == 0 {
        return 0;
    }

    let n: usize = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut cells: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        let mut j: usize = 0;
        while j < n {
            cells.push(grid[i][j]);
            j += 1;
        }
        i += 1;
    }

    let mut best: i64 = 0;
    let mut r0: usize = 0;
    while r0 < m {
        let mut c0: usize = 0;
        while c0 < n {
            let start: usize = r0 * n + c0;
            if cells[start] == 1 {
                let mut area: i64 = 0;
                let mut sr: Vec<usize> = Vec::new();
                let mut sc: Vec<usize> = Vec::new();
                let mut top: usize = 0;

                sr.push(r0);
                sc.push(c0);
                top = 1;
                cells[start] = 0;

                while top > 0 {
                    top = top - 1;
                    let r: usize = sr[top];
                    let c: usize = sc[top];
                    area = area + 1;

                    if r > 0 {
                        let nr: usize = r - 1;
                        let np: usize = nr * n + c;
                        if cells[np] == 1 {
                            cells[np] = 0;
                            if top < sr.len() {
                                sr[top] = nr;
                                sc[top] = c;
                            } else {
                                sr.push(nr);
                                sc.push(c);
                            }
                            top = top + 1;
                        }
                    }

                    if r + 1 < m {
                        let nr: usize = r + 1;
                        let np: usize = nr * n + c;
                        if cells[np] == 1 {
                            cells[np] = 0;
                            if top < sr.len() {
                                sr[top] = nr;
                                sc[top] = c;
                            } else {
                                sr.push(nr);
                                sc.push(c);
                            }
                            top = top + 1;
                        }
                    }

                    if c > 0 {
                        let nc: usize = c - 1;
                        let np: usize = r * n + nc;
                        if cells[np] == 1 {
                            cells[np] = 0;
                            if top < sr.len() {
                                sr[top] = r;
                                sc[top] = nc;
                            } else {
                                sr.push(r);
                                sc.push(nc);
                            }
                            top = top + 1;
                        }
                    }

                    if c + 1 < n {
                        let nc: usize = c + 1;
                        let np: usize = r * n + nc;
                        if cells[np] == 1 {
                            cells[np] = 0;
                            if top < sr.len() {
                                sr[top] = r;
                                sc[top] = nc;
                            } else {
                                sr.push(r);
                                sc.push(nc);
                            }
                            top = top + 1;
                        }
                    }
                }

                if area > best {
                    best = area;
                }
            }
            c0 += 1;
        }
        r0 += 1;
    }

    best
}
