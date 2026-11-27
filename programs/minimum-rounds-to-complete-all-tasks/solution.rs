pub fn minimum_rounds(tasks: &[i64]) -> i64 {
    let n = tasks.len();

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(tasks[i]);
        i += 1;
    }

    // Bottom-up merge sort the copied task difficulties.
    if n > 1 {
        let mut temp: Vec<i64> = Vec::new();
        let mut t: usize = 0;
        while t < n {
            temp.push(0);
            t += 1;
        }

        let mut width: usize = 1;
        while width < n {
            let mut start: usize = 0;
            while start < n {
                let mid = if start + width < n { start + width } else { n };
                let end = if start + 2 * width < n { start + 2 * width } else { n };

                let mut l = start;
                let mut r = mid;
                let mut k = start;

                while l < mid && r < end {
                    if v[l] <= v[r] {
                        temp[k] = v[l];
                        l += 1;
                    } else {
                        temp[k] = v[r];
                        r += 1;
                    }
                    k += 1;
                }

                while l < mid {
                    temp[k] = v[l];
                    l += 1;
                    k += 1;
                }

                while r < end {
                    temp[k] = v[r];
                    r += 1;
                    k += 1;
                }

                start = end;
            }

            let mut p: usize = 0;
            while p < n {
                v[p] = temp[p];
                p += 1;
            }

            width = width * 2;
        }
    }

    let mut ans: i64 = 0;
    let mut idx: usize = 0;

    while idx < n {
        let cur = v[idx];
        let mut cnt: i64 = 0;

        while idx < n {
            if v[idx] != cur {
                break;
            }
            cnt += 1;
            idx += 1;
        }

        if cnt == 1 {
            return -1;
        }

        ans += (cnt + 2) / 3;
    }

    ans
}
