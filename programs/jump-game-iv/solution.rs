fn filled_i64(n: usize, x: i64) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(x);
        i += 1;
    }
    v
}

fn bytes_zero(n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

pub fn min_jumps(arr: &[i64]) -> i64 {
    let n: usize = arr.len();
    let mut res: i64 = 0;

    if n > 1 {
        let mut vals: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            vals.push(arr[i]);
            i += 1;
        }

        // Iterative stable merge sort of `vals`.
        let mut buf: Vec<i64> = filled_i64(n, 0);
        let mut width: usize = 1;
        while width < n {
            let mut left: usize = 0;
            while left < n {
                let mut mid: usize = left + width;
                if mid > n {
                    mid = n;
                }
                let mut right: usize = left + width + width;
                if right > n {
                    right = n;
                }

                let mut a: usize = left;
                let mut b: usize = mid;
                let mut k: usize = left;

                while a < mid && b < right {
                    if vals[a] <= vals[b] {
                        buf[k] = vals[a];
                        a += 1;
                    } else {
                        buf[k] = vals[b];
                        b += 1;
                    }
                    k += 1;
                }
                while a < mid {
                    buf[k] = vals[a];
                    a += 1;
                    k += 1;
                }
                while b < right {
                    buf[k] = vals[b];
                    b += 1;
                    k += 1;
                }

                left = right;
            }

            let mut t: usize = 0;
            while t < n {
                vals[t] = buf[t];
                t += 1;
            }

            width = width * 2;
        }

        // Unique sorted values.
        let mut uniq: Vec<i64> = Vec::new();
        i = 0;
        while i < n {
            if i == 0 {
                uniq.push(vals[i]);
            } else if vals[i] != vals[i - 1] {
                uniq.push(vals[i]);
            }
            i += 1;
        }
        let m: usize = uniq.len();

        // Coordinate-compress each array position to a group id.
        let mut ids: Vec<i64> = filled_i64(n, 0);
        i = 0;
        while i < n {
            let x: i64 = arr[i];
            let mut lo: usize = 0;
            let mut hi: usize = m;
            while lo < hi {
                let mid: usize = (lo + hi) / 2;
                if uniq[mid] < x {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }
            ids[i] = lo as i64;
            i += 1;
        }

        // Count how many indices belong to each group.
        let mut cnt: Vec<i64> = filled_i64(m, 0);
        i = 0;
        while i < n {
            let g: usize = ids[i] as usize;
            cnt[g] = cnt[g] + 1;
            i += 1;
        }

        // Prefix offsets into a flat positions array.
        let mut start: Vec<i64> = filled_i64(m + 1, 0);
        let mut g: usize = 0;
        while g < m {
            start[g + 1] = start[g] + cnt[g];
            g += 1;
        }

        let mut nextpos: Vec<i64> = filled_i64(m, 0);
        let mut positions: Vec<i64> = filled_i64(n, 0);
        i = 0;
        while i < n {
            let gid: usize = ids[i] as usize;
            let pos: i64 = start[gid] + nextpos[gid];
            positions[pos as usize] = i as i64;
            nextpos[gid] = nextpos[gid] + 1;
            i += 1;
        }

        // BFS over the graph (no early returns inside loops).
        let mut dist: Vec<i64> = filled_i64(n, -1);
        let mut queue: Vec<i64> = filled_i64(n, 0);
        let mut used_group: Vec<u8> = bytes_zero(m);

        dist[0] = 0;
        queue[0] = 0;
        let mut qhead: usize = 0;
        let mut qtail: usize = 1;

        while qhead < qtail {
            let u: usize = queue[qhead] as usize;
            qhead += 1;
            let d: i64 = dist[u];
            let nd: i64 = d + 1;

            if u > 0 {
                if dist[u - 1] < 0 {
                    dist[u - 1] = nd;
                    queue[qtail] = (u - 1) as i64;
                    qtail += 1;
                }
            }

            if u + 1 < n {
                if dist[u + 1] < 0 {
                    dist[u + 1] = nd;
                    queue[qtail] = (u + 1) as i64;
                    qtail += 1;
                }
            }

            let gid: usize = ids[u] as usize;
            if used_group[gid] == 0 {
                used_group[gid] = 1;
                let mut k: i64 = start[gid];
                let end: i64 = start[gid + 1];
                while k < end {
                    let v: usize = positions[k as usize] as usize;
                    if dist[v] < 0 {
                        dist[v] = nd;
                        queue[qtail] = v as i64;
                        qtail += 1;
                    }
                    k += 1;
                }
            }
        }

        res = dist[n - 1];
    }

    res
}
