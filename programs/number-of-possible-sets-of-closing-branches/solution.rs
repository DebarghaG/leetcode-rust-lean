pub fn number_of_sets(n: i64, maxDistance: i64, roads: &[Vec<i64>]) -> i64 {
    let n_us = n as usize;

    let mut total: usize = 1;
    let mut p: usize = 0;
    while p < n_us {
        total = total * 2;
        p += 1;
    }

    let inf: i64 = 1000000000;
    let mut ans: i64 = 0;
    let mut mask: usize = 0;

    while mask < total {
        let mut cnt: usize = 0;
        let mut i: usize = 0;
        while i < n_us {
            if ((mask >> i) & 1) == 1 {
                cnt += 1;
            }
            i += 1;
        }

        let mut valid: bool = true;

        if cnt >= 2 {
            let size = n_us * n_us;
            let mut dist: Vec<i64> = Vec::new();
            let mut t: usize = 0;
            while t < size {
                dist.push(inf);
                t += 1;
            }

            i = 0;
            while i < n_us {
                if ((mask >> i) & 1) == 1 {
                    dist[i * n_us + i] = 0;
                }
                i += 1;
            }

            let mut r: usize = 0;
            while r < roads.len() {
                let u = roads[r][0] as usize;
                let v = roads[r][1] as usize;
                let w = roads[r][2];

                if (((mask >> u) & 1) == 1) && (((mask >> v) & 1) == 1) {
                    let idx1 = u * n_us + v;
                    if w < dist[idx1] {
                        dist[idx1] = w;
                    }

                    let idx2 = v * n_us + u;
                    if w < dist[idx2] {
                        dist[idx2] = w;
                    }
                }

                r += 1;
            }

            let mut k: usize = 0;
            while k < n_us {
                let mut ii: usize = 0;
                while ii < n_us {
                    let dik = dist[ii * n_us + k];
                    if dik < inf {
                        let mut j: usize = 0;
                        while j < n_us {
                            let dkj = dist[k * n_us + j];
                            if dkj < inf {
                                let alt = dik + dkj;
                                let idx = ii * n_us + j;
                                if alt < dist[idx] {
                                    dist[idx] = alt;
                                }
                            }
                            j += 1;
                        }
                    }
                    ii += 1;
                }
                k += 1;
            }

            i = 0;
            while i < n_us {
                if ((mask >> i) & 1) == 1 {
                    let mut j: usize = 0;
                    while j < n_us {
                        if ((mask >> j) & 1) == 1 {
                            if dist[i * n_us + j] > maxDistance {
                                valid = false;
                            }
                        }
                        j += 1;
                    }
                }
                i += 1;
            }
        }

        if valid {
            ans += 1;
        }

        mask += 1;
    }

    ans
}
