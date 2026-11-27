pub fn finding_users_active_minutes(logs: &[Vec<i64>], k: i64) -> Vec<i64> {
    let n = logs.len();
    let mut keys: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let id = logs[i][0];
        let time = logs[i][1];
        keys.push(id * 100001 + time);
        i += 1;
    }

    let m = keys.len();

    // Iterative merge sort of keys.
    if m > 1 {
        let mut tmp: Vec<i64> = Vec::new();
        let mut z = 0;
        while z < m {
            tmp.push(0);
            z += 1;
        }

        let mut width: usize = 1;
        while width < m {
            let mut start: usize = 0;
            while start < m {
                let mut mid = start + width;
                if mid > m {
                    mid = m;
                }

                let mut end = start + 2 * width;
                if end > m {
                    end = m;
                }

                let mut p = start;
                let mut q = mid;
                let mut r = start;

                while p < mid && q < end {
                    if keys[p] <= keys[q] {
                        tmp[r] = keys[p];
                        p += 1;
                    } else {
                        tmp[r] = keys[q];
                        q += 1;
                    }
                    r += 1;
                }

                while p < mid {
                    tmp[r] = keys[p];
                    p += 1;
                    r += 1;
                }

                while q < end {
                    tmp[r] = keys[q];
                    q += 1;
                    r += 1;
                }

                start += 2 * width;
            }

            let mut j = 0;
            while j < m {
                keys[j] = tmp[j];
                j += 1;
            }

            width *= 2;
        }
    }

    let mut ans: Vec<i64> = Vec::new();

    if k <= 0 {
        return ans;
    }

    let ku = k as usize;
    let mut a = 0;
    while a < ku {
        ans.push(0);
        a += 1;
    }

    let mut idx: usize = 0;
    let mut prev_id: i64 = -1;
    let mut has_prev = false;
    let mut uam: i64 = 0;

    while idx < m {
        let cur = keys[idx];

        while idx < m && keys[idx] == cur {
            idx += 1;
        }

        let id = cur / 100001;

        if !has_prev {
            prev_id = id;
            has_prev = true;
            uam = 1;
        } else if id == prev_id {
            uam += 1;
        } else {
            if uam > 0 && uam <= k {
                let pos = (uam - 1) as usize;
                if pos < ans.len() {
                    ans[pos] += 1;
                }
            }
            prev_id = id;
            uam = 1;
        }
    }

    if has_prev && uam > 0 && uam <= k {
        let pos = (uam - 1) as usize;
        if pos < ans.len() {
            ans[pos] += 1;
        }
    }

    ans
}
