pub fn construct_product_matrix(grid: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = grid.len();
    if n == 0 {
        return Vec::new();
    }

    let cols = grid[0].len();
    let modulus: i64 = 12345;
    let total = n * cols;

    let mut prefix: Vec<i64> = Vec::new();
    let mut prod: i64 = 1;
    let mut i: usize = 0;
    while i < total {
        prefix.push(prod);
        let r = i / cols;
        let c = i % cols;
        prod = (prod * (grid[r][c] % modulus)) % modulus;
        i += 1;
    }

    let mut suffix_rev: Vec<i64> = Vec::new();
    let mut suffix: i64 = 1;
    let mut j: usize = total;
    while j > 0 {
        let pos = j - 1;
        suffix_rev.push(suffix);
        let r = pos / cols;
        let c = pos % cols;
        suffix = (suffix * (grid[r][c] % modulus)) % modulus;
        j -= 1;
    }

    let mut flat: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < total {
        let after = suffix_rev[total - 1 - p];
        let value = (prefix[p] * after) % modulus;
        flat.push(value);
        p += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut r: usize = 0;
    while r < n {
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < cols {
            row.push(flat[r * cols + c]);
            c += 1;
        }
        out.push(row);
        r += 1;
    }

    out
}
