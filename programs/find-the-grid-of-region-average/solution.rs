pub fn result_grid(image: &[Vec<i64>], threshold: i64) -> Vec<Vec<i64>> {
    let m = image.len();
    let n = image[0].len();
    let total = m * n;

    let mut sum: Vec<i64> = Vec::new();
    let mut cnt: Vec<i64> = Vec::new();

    let mut idx = 0;
    while idx < total {
        sum.push(0);
        cnt.push(0);
        idx += 1;
    }

    if m >= 3 && n >= 3 {
        let mut i = 0;
        while i + 2 < m {
            let mut j = 0;
            while j + 2 < n {
                let mut ok = true;

                let mut r = 0;
                while r < 3 {
                    let mut c = 0;
                    while c < 3 {
                        let a = image[i + r][j + c];

                        if c + 1 < 3 {
                            let b = image[i + r][j + c + 1];
                            let diff = if a > b { a - b } else { b - a };
                            if diff > threshold {
                                ok = false;
                            }
                        }

                        if r + 1 < 3 {
                            let b = image[i + r + 1][j + c];
                            let diff = if a > b { a - b } else { b - a };
                            if diff > threshold {
                                ok = false;
                            }
                        }

                        c += 1;
                    }
                    r += 1;
                }

                if ok {
                    let mut region_sum: i64 = 0;

                    let mut rr = 0;
                    while rr < 3 {
                        let mut cc = 0;
                        while cc < 3 {
                            region_sum = region_sum + image[i + rr][j + cc];
                            cc += 1;
                        }
                        rr += 1;
                    }

                    let avg = region_sum / 9;

                    rr = 0;
                    while rr < 3 {
                        let mut cc = 0;
                        while cc < 3 {
                            let pos = (i + rr) * n + (j + cc);
                            let old_sum = sum[pos];
                            sum[pos] = old_sum + avg;
                            let old_cnt = cnt[pos];
                            cnt[pos] = old_cnt + 1;
                            cc += 1;
                        }
                        rr += 1;
                    }
                }

                j += 1;
            }
            i += 1;
        }
    }

    let mut result: Vec<Vec<i64>> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            let pos = i * n + j;
            let val = if cnt[pos] == 0 {
                image[i][j]
            } else {
                sum[pos] / cnt[pos]
            };
            row.push(val);
            j += 1;
        }
        result.push(row);
        i += 1;
    }

    result
}
