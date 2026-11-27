pub fn flood_fill(image: &[Vec<i64>], sr: i64, sc: i64, color: i64) -> Vec<Vec<i64>> {
    let m = image.len();
    if m == 0 {
        return Vec::new();
    }
    let n = image[0].len();

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            row.push(image[i][j]);
            j += 1;
        }
        out.push(row);
        i += 1;
    }

    let sr_u = sr as usize;
    let sc_u = sc as usize;
    let original = out[sr_u][sc_u];

    if original == color {
        return out;
    }

    let mut queue: Vec<usize> = Vec::new();
    out[sr_u][sc_u] = color;
    queue.push(sr_u * n + sc_u);

    let mut head: usize = 0;
    while head < queue.len() {
        let pos = queue[head];
        head += 1;

        let r = pos / n;
        let c = pos % n;

        if r > 0 {
            let nr = r - 1;
            if out[nr][c] == original {
                out[nr][c] = color;
                queue.push(nr * n + c);
            }
        }

        if r + 1 < m {
            let nr = r + 1;
            if out[nr][c] == original {
                out[nr][c] = color;
                queue.push(nr * n + c);
            }
        }

        if c > 0 {
            let nc = c - 1;
            if out[r][nc] == original {
                out[r][nc] = color;
                queue.push(r * n + nc);
            }
        }

        if c + 1 < n {
            let nc = c + 1;
            if out[r][nc] == original {
                out[r][nc] = color;
                queue.push(r * n + nc);
            }
        }
    }

    out
}
