pub fn len_of_v_diagonal(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }
    let m = grid[0].len();
    if m == 0 {
        return 0;
    }

    let total: usize = n * m;
    let limit: usize = 8 * total;

    // dp1[(direction * 2 + parity) * total + index]
    // parity 0 => next expected value is 2
    // parity 1 => next expected value is 0
    // This table assumes the single clockwise turn has already been used.
    let mut dp1: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < limit {
        dp1.push(0);
        z += 1;
    }

    let mut d: usize = 0;
    while d < 4 {
        let dr: i64;
        let dc: i64;
        if d == 0 {
            dr = 1;
            dc = 1;
        } else if d == 1 {
            dr = 1;
            dc = -1;
        } else if d == 2 {
            dr = -1;
            dc = -1;
        } else {
            dr = -1;
            dc = 1;
        }

        let mut step: usize = 0;
        while step < n {
            let i: usize = if dr == 1 { n - 1 - step } else { step };
            let mut j: usize = 0;
            while j < m {
                let idx: usize = i * m + j;

                let mut ni: usize = i;
                let mut nj: usize = j;
                let mut inside: bool = true;

                if dr == 1 {
                    if i + 1 < n {
                        ni = i + 1;
                    } else {
                        inside = false;
                    }
                } else {
                    if i > 0 {
                        ni = i - 1;
                    } else {
                        inside = false;
                    }
                }

                if dc == 1 {
                    if j + 1 < m {
                        nj = j + 1;
                    } else {
                        inside = false;
                    }
                } else {
                    if j > 0 {
                        nj = j - 1;
                    } else {
                        inside = false;
                    }
                }

                let mut p: usize = 0;
                while p < 2 {
                    let expected: i64 = if p == 0 { 2 } else { 0 };

                    if inside {
                        if grid[ni][nj] == expected {
                            let np: usize = 1 - p;
                            let nidx: usize = ni * m + nj;
                            dp1[(d * 2 + p) * total + idx] =
                                1 + dp1[(d * 2 + np) * total + nidx];
                        }
                    }

                    p += 1;
                }

                j += 1;
            }
            step += 1;
        }

        d += 1;
    }

    // dp0[(direction * 2 + parity) * total + index]
    // This table assumes the clockwise turn has not been used yet.
    let mut dp0: Vec<i64> = Vec::new();
    z = 0;
    while z < limit {
        dp0.push(0);
        z += 1;
    }

    d = 0;
    while d < 4 {
        let dr: i64;
        let dc: i64;
        if d == 0 {
            dr = 1;
            dc = 1;
        } else if d == 1 {
            dr = 1;
            dc = -1;
        } else if d == 2 {
            dr = -1;
            dc = -1;
        } else {
            dr = -1;
            dc = 1;
        }

        let d2: usize = if d == 3 { 0 } else { d + 1 };

        let dr2: i64;
        let dc2: i64;
        if d2 == 0 {
            dr2 = 1;
            dc2 = 1;
        } else if d2 == 1 {
            dr2 = 1;
            dc2 = -1;
        } else if d2 == 2 {
            dr2 = -1;
            dc2 = -1;
        } else {
            dr2 = -1;
            dc2 = 1;
        }

        let mut step: usize = 0;
        while step < n {
            let i: usize = if dr == 1 { n - 1 - step } else { step };
            let mut j: usize = 0;
            while j < m {
                let idx: usize = i * m + j;

                let mut ni: usize = i;
                let mut nj: usize = j;
                let mut inside: bool = true;

                if dr == 1 {
                    if i + 1 < n {
                        ni = i + 1;
                    } else {
                        inside = false;
                    }
                } else {
                    if i > 0 {
                        ni = i - 1;
                    } else {
                        inside = false;
                    }
                }

                if dc == 1 {
                    if j + 1 < m {
                        nj = j + 1;
                    } else {
                        inside = false;
                    }
                } else {
                    if j > 0 {
                        nj = j - 1;
                    } else {
                        inside = false;
                    }
                }

                let mut ti: usize = i;
                let mut tj: usize = j;
                let mut tinside: bool = true;

                if dr2 == 1 {
                    if i + 1 < n {
                        ti = i + 1;
                    } else {
                        tinside = false;
                    }
                } else {
                    if i > 0 {
                        ti = i - 1;
                    } else {
                        tinside = false;
                    }
                }

                if dc2 == 1 {
                    if j + 1 < m {
                        tj = j + 1;
                    } else {
                        tinside = false;
                    }
                } else {
                    if j > 0 {
                        tj = j - 1;
                    } else {
                        tinside = false;
                    }
                }

                let mut p: usize = 0;
                while p < 2 {
                    let expected: i64 = if p == 0 { 2 } else { 0 };
                    let mut best: i64 = 0;

                    if inside {
                        if grid[ni][nj] == expected {
                            let np: usize = 1 - p;
                            let nidx: usize = ni * m + nj;
                            let cand: i64 = 1 + dp0[(d * 2 + np) * total + nidx];
                            if cand > best {
                                best = cand;
                            }
                        }
                    }

                    if tinside {
                        if grid[ti][tj] == expected {
                            let np: usize = 1 - p;
                            let tidx: usize = ti * m + tj;
                            let cand: i64 = 1 + dp1[(d2 * 2 + np) * total + tidx];
                            if cand > best {
                                best = cand;
                            }
                        }
                    }

                    dp0[(d * 2 + p) * total + idx] = best;
                    p += 1;
                }

                j += 1;
            }
            step += 1;
        }

        d += 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < m {
            if grid[i][j] == 1 {
                let idx: usize = i * m + j;
                let mut best_add: i64 = 0;
                let mut dd: usize = 0;

                while dd < 4 {
                    let val: i64 = dp0[(dd * 2) * total + idx];
                    if val > best_add {
                        best_add = val;
                    }
                    dd += 1;
                }

                let cur_len: i64 = 1 + best_add;
                if cur_len > ans {
                    ans = cur_len;
                }
            }

            j += 1;
        }
        i += 1;
    }

    ans
}
