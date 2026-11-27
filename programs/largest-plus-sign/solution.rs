fn bit_add(tree: &mut Vec<i64>, n: usize, idx: usize, delta: i64) {
    let mut i: usize = idx + 1;
    while i <= n {
        tree[i] = tree[i] + delta;
        let lb: usize = i & (i ^ (i - 1));
        i += lb;
    }
}

fn bit_sum(tree: &Vec<i64>, i0: usize) -> i64 {
    let mut i: usize = i0;
    let mut s: i64 = 0;
    while i > 0 {
        s = s + tree[i];
        let lb: usize = i & (i ^ (i - 1));
        i -= lb;
    }
    s
}

fn bit_query(tree: &Vec<i64>, start: usize, end: usize) -> i64 {
    let a: i64 = bit_sum(tree, end + 1);
    let b: i64 = bit_sum(tree, start);
    a - b
}

fn check(n: usize, rows: &[Vec<i64>], k: usize) -> bool {
    if k == 0 {
        return true;
    }
    if 2 * k - 1 > n {
        return false;
    }

    let lo: usize = k - 1;
    let hi: usize = n - k;

    let mut col_count: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < n {
        col_count.push(0);
        c += 1;
    }

    let mut tree: Vec<i64> = Vec::new();
    c = 0;
    while c <= n {
        tree.push(0);
        c += 1;
    }
    c = 1;
    while c <= n {
        let lb: usize = c & (c ^ (c - 1));
        tree[c] = lb as i64;
        c += 1;
    }

    let init_end: usize = 2 * k - 1;
    let mut x: usize = 0;
    while x < init_end {
        let row = &rows[x];
        let d: usize = row.len();
        let mut t: usize = 0;
        while t < d {
            let y: usize = row[t] as usize;
            if col_count[y] == 0 {
                bit_add(&mut tree, n, y, -1);
            }
            col_count[y] = col_count[y] + 1;
            t += 1;
        }
        x += 1;
    }

    let mut found: bool = false;
    let mut r: usize = lo;
    while r <= hi {
        if !found {
            let row = &rows[r];
            let d: usize = row.len();
            let mut idx: usize = 0;
            while idx <= d {
                if !found {
                    let a64: i64 = if idx == 0 { -1 } else { row[idx - 1] };
                    let b64: i64 = if idx < d { row[idx] } else { n as i64 };
                    let start64: i64 = a64 + (k as i64);
                    let end64: i64 = b64 - (k as i64);

                    let mut lo_c: i64 = start64;
                    if lo_c < (lo as i64) {
                        lo_c = lo as i64;
                    }
                    let mut hi_c: i64 = end64;
                    if hi_c > (hi as i64) {
                        hi_c = hi as i64;
                    }

                    if lo_c <= hi_c {
                        if hi_c >= 0 {
                            let cnt: i64 = bit_query(&tree, lo_c as usize, hi_c as usize);
                            if cnt > 0 {
                                found = true;
                            }
                        }
                    }
                }
                idx += 1;
            }

            if !found {
                if r < hi {
                    let add_x: usize = r + k;
                    let row_add = &rows[add_x];
                    let da: usize = row_add.len();
                    let mut t: usize = 0;
                    while t < da {
                        let y: usize = row_add[t] as usize;
                        if col_count[y] == 0 {
                            bit_add(&mut tree, n, y, -1);
                        }
                        col_count[y] = col_count[y] + 1;
                        t += 1;
                    }

                    let rem_x: usize = r + 1 - k;
                    let row_rem = &rows[rem_x];
                    let dr: usize = row_rem.len();
                    t = 0;
                    while t < dr {
                        let y: usize = row_rem[t] as usize;
                        col_count[y] = col_count[y] - 1;
                        if col_count[y] == 0 {
                            bit_add(&mut tree, n, y, 1);
                        }
                        t += 1;
                    }
                }
            }
        }
        r += 1;
    }

    found
}

pub fn order_of_largest_plus_sign(n: i64, mines: &[Vec<i64>]) -> i64 {
    let n_usize: usize = n as usize;

    let mut rows: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        let v: Vec<i64> = Vec::new();
        rows.push(v);
        i += 1;
    }

    i = 0;
    while i < mines.len() {
        let x: usize = mines[i][0] as usize;
        let y: i64 = mines[i][1];
        rows[x].push(y);
        i += 1;
    }

    i = 0;
    while i < n_usize {
        let len: usize = rows[i].len();
        let mut a: usize = 1;
        while a < len {
            let key: i64 = rows[i][a];
            let mut b: usize = a;
            let mut keep: bool = true;
            while keep {
                if b > 0 {
                    if rows[i][b - 1] > key {
                        rows[i][b] = rows[i][b - 1];
                        b -= 1;
                    } else {
                        keep = false;
                    }
                } else {
                    keep = false;
                }
            }
            rows[i][b] = key;
            a += 1;
        }
        i += 1;
    }

    let mut low: usize = 0;
    let mut high: usize = (n_usize + 1) / 2;
    while low < high {
        let mid: usize = (low + high + 1) / 2;
        if check(n_usize, &rows, mid) {
            low = mid;
        } else {
            high = mid - 1;
        }
    }

    low as i64
}
