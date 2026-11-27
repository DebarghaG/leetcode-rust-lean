pub fn find_rotation(mat: &[Vec<i64>], target: &[Vec<i64>]) -> bool {
    let n = mat.len();
    if n == 0 {
        return true;
    }

    let mut rot: usize = 0;
    while rot < 4 {
        let mut same = true;
        let mut i: usize = 0;

        while i < n {
            let mut j: usize = 0;

            while j < n {
                let mut si: usize = i;
                let mut sj: usize = j;

                if rot == 1 {
                    si = n - 1 - j;
                    sj = i;
                } else if rot == 2 {
                    si = n - 1 - i;
                    sj = n - 1 - j;
                } else if rot == 3 {
                    si = j;
                    sj = n - 1 - i;
                }

                if mat[si][sj] != target[i][j] {
                    same = false;
                }

                j += 1;
            }

            i += 1;
        }

        if same {
            return true;
        }

        rot += 1;
    }

    false
}
