pub fn least_bricks(wall: &[Vec<i64>]) -> i64 {
    let n: i64 = wall.len() as i64;
    let mut edges: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < wall.len() {
        let row = &wall[i];
        let m = row.len();
        let mut prefix: i64 = 0;
        let mut j: usize = 0;

        // Only internal brick edges count; exclude the right border.
        while j + 1 < m {
            prefix = prefix + row[j];
            edges.push(prefix);
            j = j + 1;
        }

        i = i + 1;
    }

    let len = edges.len();
    if len == 0 {
        return n;
    }

    // Bottom-up merge sort of `edges`.
    let mut tmp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < len {
        tmp.push(0);
        t = t + 1;
    }

    let mut width: usize = 1;
    while width < len {
        let mut start: usize = 0;

        while start < len {
            let mid = min_usize(start + width, len);
            let end = min_usize(start + width + width, len);

            let mut p = start;
            let mut q = mid;
            let mut k = start;

            while p < mid && q < end {
                if edges[p] <= edges[q] {
                    tmp[k] = edges[p];
                    p = p + 1;
                } else {
                    tmp[k] = edges[q];
                    q = q + 1;
                }
                k = k + 1;
            }

            while p < mid {
                tmp[k] = edges[p];
                p = p + 1;
                k = k + 1;
            }

            while q < end {
                tmp[k] = edges[q];
                q = q + 1;
                k = k + 1;
            }

            start = start + width + width;
        }

        let mut c: usize = 0;
        while c < len {
            edges[c] = tmp[c];
            c = c + 1;
        }

        width = width + width;
    }

    // Find the maximum frequency of any internal edge position.
    let mut best: i64 = 0;
    let mut idx: usize = 0;

    while idx < len {
        let val = edges[idx];
        let mut cnt: i64 = 0;

        while idx < len && edges[idx] == val {
            cnt = cnt + 1;
            idx = idx + 1;
        }

        if cnt > best {
            best = cnt;
        }
    }

    n - best
}

fn min_usize(a: usize, b: usize) -> usize {
    if a < b {
        a
    } else {
        b
    }
}
