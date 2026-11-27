pub fn smallest_common_element(mat: &[Vec<i64>]) -> i64 {
    if mat.len() == 0 {
        return -1;
    }

    let mut candidates: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < mat[0].len() {
        candidates.push(mat[0][j]);
        j += 1;
    }

    if candidates.len() == 0 {
        return -1;
    }

    let mut i: usize = 1;
    while i < mat.len() {
        let row = &mat[i];
        let mut next: Vec<i64> = Vec::new();

        let mut a: usize = 0;
        let mut b: usize = 0;

        while a < candidates.len() && b < row.len() {
            let x = candidates[a];
            let y = row[b];

            if x == y {
                next.push(x);
                a += 1;
                b += 1;
            } else if x < y {
                a += 1;
            } else {
                b += 1;
            }
        }

        if next.len() == 0 {
            return -1;
        }

        candidates = next;
        i += 1;
    }

    candidates[0]
}
