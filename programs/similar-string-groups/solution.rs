pub fn num_similar_groups(strs: &[Vec<u8>]) -> i64 {
    let n = strs.len();

    let mut parent: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        parent.push(i as i64);
        i += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let len_i = strs[i].len();
            let len_j = strs[j].len();
            let mut m = len_i;
            if len_j < m {
                m = len_j;
            }

            let mut diff: i64 = 0;
            let mut k: usize = 0;
            while k < m {
                if strs[i][k] != strs[j][k] {
                    diff += 1;
                }
                k += 1;
            }

            if diff <= 2 {
                let mut ri = i as i64;
                while parent[ri as usize] != ri {
                    ri = parent[ri as usize];
                }

                let mut rj = j as i64;
                while parent[rj as usize] != rj {
                    rj = parent[rj as usize];
                }

                if ri != rj {
                    parent[ri as usize] = rj;
                }
            }

            j += 1;
        }
        i += 1;
    }

    let mut groups: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut r = i as i64;
        while parent[r as usize] != r {
            r = parent[r as usize];
        }
        if r == i as i64 {
            groups += 1;
        }
        i += 1;
    }

    groups
}
