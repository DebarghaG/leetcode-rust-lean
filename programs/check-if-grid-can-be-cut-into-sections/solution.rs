fn count_sections(rectangles: &[Vec<i64>], axis: i64) -> i64 {
    let m = rectangles.len();
    if m == 0 {
        return 0;
    }

    let base: i64 = 1000000001;
    let mut codes: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < m {
        let row = &rectangles[i];
        let s: i64;
        let e: i64;

        if axis == 0 {
            s = row[0];
            e = row[2];
        } else {
            s = row[1];
            e = row[3];
        }

        codes.push(s * base + e);
        i += 1;
    }

    let len = codes.len();

    if len > 1 {
        let mut buf: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < len {
            buf.push(0);
            j += 1;
        }

        let mut width: usize = 1;
        while width < len {
            let mut start: usize = 0;

            while start < len {
                let mid = if start + width < len {
                    start + width
                } else {
                    len
                };

                let end = if start + width + width < len {
                    start + width + width
                } else {
                    len
                };

                let mut l = start;
                let mut r = mid;
                let mut k = start;

                while l < mid && r < end {
                    if codes[l] <= codes[r] {
                        buf[k] = codes[l];
                        l += 1;
                    } else {
                        buf[k] = codes[r];
                        r += 1;
                    }
                    k += 1;
                }

                while l < mid {
                    buf[k] = codes[l];
                    l += 1;
                    k += 1;
                }

                while r < end {
                    buf[k] = codes[r];
                    r += 1;
                    k += 1;
                }

                start = start + width + width;
            }

            let mut copy_idx: usize = 0;
            while copy_idx < len {
                codes[copy_idx] = buf[copy_idx];
                copy_idx += 1;
            }

            width = width + width;
        }
    }

    let mut sections: i64 = 1;
    let mut current_end: i64 = codes[0] % base;
    let mut idx: usize = 1;

    while idx < len {
        let c = codes[idx];
        let s = c / base;
        let e = c % base;

        if s >= current_end {
            sections += 1;
            current_end = e;
        } else if e > current_end {
            current_end = e;
        }

        idx += 1;
    }

    sections
}

pub fn check_valid_cuts(n: i64, rectangles: &[Vec<i64>]) -> bool {
    let _ = n;

    if count_sections(rectangles, 0) >= 3 {
        return true;
    }

    if count_sections(rectangles, 1) >= 3 {
        return true;
    }

    false
}
