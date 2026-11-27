pub fn count_black_blocks(m: i64, n: i64, coordinates: &[Vec<i64>]) -> Vec<i64> {
    let mut keys: Vec<i64> = Vec::new();

    let coord_len = coordinates.len();
    let mut pos: usize = 0;
    while pos < coord_len {
        let x = coordinates[pos][0];
        let y = coordinates[pos][1];

        let mut dx: i64 = -1;
        while dx <= 0 {
            let mut dy: i64 = -1;
            while dy <= 0 {
                let bx = x + dx;
                let by = y + dy;

                if bx >= 0 && bx < m - 1 && by >= 0 && by < n - 1 {
                    let key = bx * (n - 1) + by;
                    keys.push(key);
                }

                dy += 1;
            }
            dx += 1;
        }

        pos += 1;
    }

    let klen = keys.len();

    // Bottom-up merge sort on keys.
    if klen > 1 {
        let mut buf: Vec<i64> = Vec::new();
        let mut p: usize = 0;
        while p < klen {
            buf.push(0);
            p += 1;
        }

        let mut width: usize = 1;
        while width < klen {
            let mut left: usize = 0;

            while left < klen {
                let mid0 = left + width;
                let mid = if mid0 < klen { mid0 } else { klen };

                let right0 = left + width + width;
                let right = if right0 < klen { right0 } else { klen };

                let mut i = left;
                let mut j = mid;
                let mut k = left;

                while i < mid && j < right {
                    if keys[i] <= keys[j] {
                        buf[k] = keys[i];
                        i += 1;
                    } else {
                        buf[k] = keys[j];
                        j += 1;
                    }
                    k += 1;
                }

                while i < mid {
                    buf[k] = keys[i];
                    i += 1;
                    k += 1;
                }

                while j < right {
                    buf[k] = keys[j];
                    j += 1;
                    k += 1;
                }

                left = left + width + width;
            }

            let mut t: usize = 0;
            while t < klen {
                keys[t] = buf[t];
                t += 1;
            }

            width = width * 2;
        }
    }

    let total_blocks = (m - 1) * (n - 1);

    let mut ans: Vec<i64> = Vec::new();
    ans.push(total_blocks);
    ans.push(0);
    ans.push(0);
    ans.push(0);
    ans.push(0);

    if klen == 0 {
        return ans;
    }

    let mut idx: usize = 0;
    while idx < klen {
        let key = keys[idx];
        let mut black_count: i64 = 0;

        while idx < klen {
            if keys[idx] != key {
                break;
            }
            black_count += 1;
            idx += 1;
        }

        ans[0] -= 1;
        let bucket = black_count as usize;
        ans[bucket] += 1;
    }

    ans
}
