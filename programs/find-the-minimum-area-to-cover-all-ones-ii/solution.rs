fn area(
    grid: &[Vec<i64>],
    r1: usize,
    r2: usize,
    c1: usize,
    c2: usize,
) -> usize {
    if r1 >= r2 {
        return 0;
    }
    if c1 >= c2 {
        return 0;
    }

    let mut found = false;
    let mut min_r: usize = 0;
    let mut max_r: usize = 0;
    let mut min_c: usize = 0;
    let mut max_c: usize = 0;

    let mut r = r1;
    while r < r2 {
        let row = &grid[r];
        let mut c = c1;
        while c < c2 {
            if row[c] == 1 {
                if !found {
                    found = true;
                    min_r = r;
                    max_r = r;
                    min_c = c;
                    max_c = c;
                } else {
                    if r < min_r {
                        min_r = r;
                    }
                    if r > max_r {
                        max_r = r;
                    }
                    if c < min_c {
                        min_c = c;
                    }
                    if c > max_c {
                        max_c = c;
                    }
                }
            }
            c += 1;
        }
        r += 1;
    }

    if !found {
        return 0;
    }

    let h = max_r - min_r + 1;
    let w = max_c - min_c + 1;
    h * w
}

pub fn minimum_sum(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }

    let m = grid[0].len();
    if m == 0 {
        return 0;
    }

    let mut ans: usize = 1_000_000_000;

    // Three horizontal strips.
    let mut i: usize = 1;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let a = area(grid, 0, i, 0, m);
            let b = area(grid, i, j, 0, m);
            let c = area(grid, j, n, 0, m);
            if a > 0 && b > 0 && c > 0 {
                let s = a + b + c;
                if s < ans {
                    ans = s;
                }
            }
            j += 1;
        }
        i += 1;
    }

    // Three vertical strips.
    let mut i: usize = 1;
    while i < m {
        let mut j: usize = i + 1;
        while j < m {
            let a = area(grid, 0, n, 0, i);
            let b = area(grid, 0, n, i, j);
            let c = area(grid, 0, n, j, m);
            if a > 0 && b > 0 && c > 0 {
                let s = a + b + c;
                if s < ans {
                    ans = s;
                }
            }
            j += 1;
        }
        i += 1;
    }

    // Horizontal split, then split the top or bottom part vertically.
    let mut h: usize = 1;
    while h < n {
        let mut c: usize = 1;
        while c < m {
            // Top part is split into two, bottom part is one rectangle.
            let a = area(grid, 0, h, 0, c);
            let b = area(grid, 0, h, c, m);
            let d = area(grid, h, n, 0, m);
            if a > 0 && b > 0 && d > 0 {
                let s = a + b + d;
                if s < ans {
                    ans = s;
                }
            }

            // Top part is one rectangle, bottom part is split into two.
            let e = area(grid, 0, h, 0, m);
            let f = area(grid, h, n, 0, c);
            let g = area(grid, h, n, c, m);
            if e > 0 && f > 0 && g > 0 {
                let s = e + f + g;
                if s < ans {
                    ans = s;
                }
            }

            c += 1;
        }
        h += 1;
    }

    // Vertical split, then split the left or right part horizontally.
    let mut c: usize = 1;
    while c < m {
        let mut h: usize = 1;
        while h < n {
            // Left part is split into two, right part is one rectangle.
            let a = area(grid, 0, h, 0, c);
            let b = area(grid, h, n, 0, c);
            let d = area(grid, 0, n, c, m);
            if a > 0 && b > 0 && d > 0 {
                let s = a + b + d;
                if s < ans {
                    ans = s;
                }
            }

            // Left part is one rectangle, right part is split into two.
            let e = area(grid, 0, n, 0, c);
            let f = area(grid, 0, h, c, m);
            let g = area(grid, h, n, c, m);
            if e > 0 && f > 0 && g > 0 {
                let s = e + f + g;
                if s < ans {
                    ans = s;
                }
            }

            h += 1;
        }
        c += 1;
    }

    ans as i64
}
