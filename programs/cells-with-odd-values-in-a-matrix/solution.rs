pub fn odd_cells(m: i64, n: i64, indices: &[Vec<i64>]) -> i64 {
    let m_usize = m as usize;
    let n_usize = n as usize;

    let mut row_parity: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < m_usize {
        row_parity.push(false);
        i += 1;
    }

    let mut col_parity: Vec<bool> = Vec::new();
    let mut j = 0;
    while j < n_usize {
        col_parity.push(false);
        j += 1;
    }

    let mut k = 0;
    while k < indices.len() {
        let r = indices[k][0] as usize;
        let c = indices[k][1] as usize;
        row_parity[r] = !row_parity[r];
        col_parity[c] = !col_parity[c];
        k += 1;
    }

    let mut row_odd: i64 = 0;
    let mut a = 0;
    while a < m_usize {
        if row_parity[a] {
            row_odd += 1;
        }
        a += 1;
    }

    let mut col_odd: i64 = 0;
    let mut b = 0;
    while b < n_usize {
        if col_parity[b] {
            col_odd += 1;
        }
        b += 1;
    }

    row_odd * (n - col_odd) + (m - row_odd) * col_odd
}
