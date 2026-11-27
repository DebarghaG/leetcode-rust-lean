pub fn num_submatrix_sum_target(matrix: &[Vec<i64>], target: i64) -> i64 {
    let n: usize = matrix.len();
    let m: usize = matrix[0].len();

    let mut total: i64 = 0;
    let mut top: usize = 0;

    while top < n {
        let mut col_sums: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < m {
            col_sums.push(0);
            j += 1;
        }

        let mut bottom: usize = top;
        while bottom < n {
            let row = &matrix[bottom];

            j = 0;
            while j < m {
                col_sums[j] += row[j];
                j += 1;
            }

            total += count_subarrays(&col_sums, target);
            bottom += 1;
        }

        top += 1;
    }

    total
}

fn count_subarrays(v: &[i64], target: i64) -> i64 {
    let cap: usize = 512;

    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    let mut used: Vec<bool> = Vec::new();

    let mut z: usize = 0;
    while z < cap {
        keys.push(0);
        counts.push(0);
        used.push(false);
        z += 1;
    }

    let mut pos: usize = ((0i64 + 10000000) % 512) as usize;
    let mut inserted: bool = false;
    while !inserted {
        if !used[pos] {
            used[pos] = true;
            keys[pos] = 0;
            counts[pos] = 1;
            inserted = true;
        } else if keys[pos] == 0 {
            counts[pos] += 1;
            inserted = true;
        } else {
            pos = (pos + 1) % cap;
        }
    }

    let mut ans: i64 = 0;
    let mut prefix: i64 = 0;
    let mut i: usize = 0;

    while i < v.len() {
        prefix += v[i];
        let need: i64 = prefix - target;

        if need >= -10000000 && need <= 10000000 {
            let mut p: usize = ((need + 10000000) % 512) as usize;
            let mut searching: bool = true;

            while searching && used[p] {
                if keys[p] == need {
                    ans += counts[p];
                    searching = false;
                } else {
                    p = (p + 1) % cap;
                }
            }
        }

        let mut p: usize = ((prefix + 10000000) % 512) as usize;
        let mut done: bool = false;

        while !done {
            if !used[p] {
                used[p] = true;
                keys[p] = prefix;
                counts[p] = 1;
                done = true;
            } else if keys[p] == prefix {
                counts[p] += 1;
                done = true;
            } else {
                p = (p + 1) % cap;
            }
        }

        i += 1;
    }

    ans
}
