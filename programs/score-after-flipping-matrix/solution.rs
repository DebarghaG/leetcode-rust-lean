pub fn matrix_score(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    let n = grid[0].len();

    let mut m_i: i64 = 0;
    let mut t: usize = 0;
    while t < m {
        m_i += 1;
        t += 1;
    }

    let mut weight: i64 = 1;
    let mut k: usize = 1;
    while k < n {
        weight *= 2;
        k += 1;
    }

    let mut score: i64 = m_i * weight;

    let mut j: usize = 1;
    while j < n {
        weight = weight / 2;

        let mut ones: i64 = 0;
        let mut i: usize = 0;
        while i < m {
            let mut bit = grid[i][j];
            if grid[i][0] == 0 {
                bit = 1 - bit;
            }
            ones += bit;
            i += 1;
        }

        let mut best = ones;
        let zeros = m_i - ones;
        if zeros > best {
            best = zeros;
        }

        score += best * weight;
        j += 1;
    }

    score
}
