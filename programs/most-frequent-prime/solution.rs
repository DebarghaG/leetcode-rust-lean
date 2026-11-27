fn is_prime(n: i64) -> bool {
    if n < 2 {
        return false;
    }
    let mut d: i64 = 2;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }
    true
}

pub fn most_frequent_prime(mat: &[Vec<i64>]) -> i64 {
    let m: usize = mat.len();
    if m == 0 {
        return -1;
    }
    let n: usize = mat[0].len();
    if n == 0 {
        return -1;
    }

    // Direction vectors: NW, N, NE, W, E, SW, S, SE
    let mut dirs_x: Vec<i64> = Vec::new();
    let mut dirs_y: Vec<i64> = Vec::new();
    dirs_x.push(-1);
    dirs_y.push(-1);
    dirs_x.push(-1);
    dirs_y.push(0);
    dirs_x.push(-1);
    dirs_y.push(1);
    dirs_x.push(0);
    dirs_y.push(-1);
    dirs_x.push(0);
    dirs_y.push(1);
    dirs_x.push(1);
    dirs_y.push(-1);
    dirs_x.push(1);
    dirs_y.push(0);
    dirs_x.push(1);
    dirs_y.push(1);

    let mut nums: Vec<i64> = Vec::new();
    let mut freqs: Vec<i64> = Vec::new();

    let m_i: i64 = m as i64;
    let n_i: i64 = n as i64;

    let mut i: usize = 0;
    while i < m {
        let mut j: usize = 0;
        while j < n {
            let mut d: usize = 0;
            while d < 8 {
                let dx: i64 = dirs_x[d];
                let dy: i64 = dirs_y[d];
                let mut val: i64 = mat[i][j];
                let mut x: i64 = i as i64 + dx;
                let mut y: i64 = j as i64 + dy;

                while x >= 0 && x < m_i && y >= 0 && y < n_i {
                    val = val * 10 + mat[x as usize][y as usize];

                    if val > 10 && is_prime(val) {
                        let len: usize = nums.len();
                        let mut found: bool = false;
                        let mut k: usize = 0;
                        while k < len {
                            if nums[k] == val {
                                freqs[k] = freqs[k] + 1;
                                found = true;
                            }
                            k += 1;
                        }
                        if !found {
                            nums.push(val);
                            freqs.push(1);
                        }
                    }

                    x = x + dx;
                    y = y + dy;
                }

                d += 1;
            }
            j += 1;
        }
        i += 1;
    }

    if nums.len() == 0 {
        return -1;
    }

    let mut best_val: i64 = -1;
    let mut best_freq: i64 = 0;
    let total: usize = nums.len();
    let mut k: usize = 0;
    while k < total {
        let v: i64 = nums[k];
        let f: i64 = freqs[k];
        if f > best_freq {
            best_freq = f;
            best_val = v;
        } else if f == best_freq && v > best_val {
            best_val = v;
        }
        k += 1;
    }

    best_val
}
