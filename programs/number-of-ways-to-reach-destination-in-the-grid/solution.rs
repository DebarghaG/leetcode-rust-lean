pub fn number_of_ways(n: i64, m: i64, k: i64, source: &[i64], dest: &[i64]) -> i64 {
    let modulo: i64 = 1000000007;

    let sr = source[0];
    let sc = source[1];
    let dr = dest[0];
    let dc = dest[1];

    let mut row_size: Vec<i64> = Vec::new();
    let mut rows: usize = 0;
    let mut src_rt: usize = 0;
    let mut dst_rt: usize = 0;

    if sr == dr {
        row_size.push(1);
        row_size.push(n - 1);
        rows = 2;
        src_rt = 0;
        dst_rt = 0;
    } else {
        row_size.push(1);
        row_size.push(1);
        row_size.push(n - 2);
        rows = 3;
        src_rt = 0;
        dst_rt = 1;
    }

    let mut col_size: Vec<i64> = Vec::new();
    let mut cols: usize = 0;
    let mut src_ct: usize = 0;
    let mut dst_ct: usize = 0;

    if sc == dc {
        col_size.push(1);
        col_size.push(m - 1);
        cols = 2;
        src_ct = 0;
        dst_ct = 0;
    } else {
        col_size.push(1);
        col_size.push(1);
        col_size.push(m - 2);
        cols = 3;
        src_ct = 0;
        dst_ct = 1;
    }

    let total = rows * cols;
    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < total {
        dp.push(0);
        z += 1;
    }

    dp[src_rt * cols + src_ct] = 1;

    let mut step: i64 = 0;
    while step < k {
        let mut ndp: Vec<i64> = Vec::new();
        let mut z2: usize = 0;
        while z2 < total {
            ndp.push(0);
            z2 += 1;
        }

        let mut i: usize = 0;
        while i < rows {
            let mut j: usize = 0;
            while j < cols {
                let val = dp[i * cols + j];

                // Move horizontally: keep the same row, change the column.
                let mut l: usize = 0;
                while l < cols {
                    let mut choices = col_size[l];
                    if l == j {
                        choices -= 1;
                    }
                    if choices > 0 {
                        let add = (val * choices) % modulo;
                        let idx = i * cols + l;
                        let cur = ndp[idx];
                        let mut nv = cur + add;
                        if nv >= modulo {
                            nv -= modulo;
                        }
                        ndp[idx] = nv;
                    }
                    l += 1;
                }

                // Move vertically: keep the same column, change the row.
                let mut p: usize = 0;
                while p < rows {
                    let mut choices = row_size[p];
                    if p == i {
                        choices -= 1;
                    }
                    if choices > 0 {
                        let add = (val * choices) % modulo;
                        let idx = p * cols + j;
                        let cur = ndp[idx];
                        let mut nv = cur + add;
                        if nv >= modulo {
                            nv -= modulo;
                        }
                        ndp[idx] = nv;
                    }
                    p += 1;
                }

                j += 1;
            }
            i += 1;
        }

        dp = ndp;
        step += 1;
    }

    dp[dst_rt * cols + dst_ct] % modulo
}
