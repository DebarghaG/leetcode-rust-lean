pub fn sort_the_students(score: &[Vec<i64>], k: i64) -> Vec<Vec<i64>> {
    let m = score.len();
    let m_i = m as i64;
    let kk = k as usize;

    // ranks[i] = number of students with a strictly greater k-th score.
    // (scores are distinct, so this is exactly student i's descending position)
    let mut ranks: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < m {
        let mut rank: i64 = 0;
        let mut j = 0usize;
        while j < m {
            if score[j][kk] > score[i][kk] {
                rank += 1;
            }
            j += 1;
        }
        ranks.push(rank);
        i += 1;
    }

    // Emit rows in ascending rank order. For each destination position p,
    // exactly one student has ranks[s] == p; copy that row and push it.
    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut p: i64 = 0;
    while p < m_i {
        let mut s = 0usize;
        while s < m {
            if ranks[s] == p {
                let n = score[s].len();
                let mut row: Vec<i64> = Vec::new();
                let mut c = 0usize;
                while c < n {
                    row.push(score[s][c]);
                    c += 1;
                }
                out.push(row);
            }
            s += 1;
        }
        p += 1;
    }

    out
}
