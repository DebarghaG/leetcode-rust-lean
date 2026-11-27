fn composition_rank(counts: &[i64], total: i64, choose: &[i64]) -> i64 {
    let mut rank: i64 = 0;
    let mut rem: i64 = total;
    let mut d: i64 = 0;

    while d < 10 {
        let c = counts[d as usize];
        let m = 9 - d;
        let mut v: i64 = 0;

        while v < c {
            let r = rem - v;
            if m == 0 {
                if r == 0 {
                    rank += 1;
                }
            } else if r >= 0 {
                let a = r + m - 1;
                let b = m - 1;
                rank += choose[(a * 10 + b) as usize];
            }
            v += 1;
        }

        rem -= c;
        d += 1;
    }

    rank
}

pub fn count_good_integers(n: i64, k: i64) -> i64 {
    // factorials up to 10
    let mut fact: Vec<i64> = Vec::new();
    fact.push(1);
    let mut i: i64 = 1;
    while i <= 10 {
        let prev = fact[(i - 1) as usize];
        fact.push(prev * i);
        i += 1;
    }

    // powers of ten
    let mut p10: Vec<i64> = Vec::new();
    let mut p: i64 = 1;
    let mut e: i64 = 0;
    while e <= 10 {
        p10.push(p);
        p = p * 10;
        e += 1;
    }

    // binomial table, flattened: choose[a * 10 + b] = C(a, b)
    let mut choose: Vec<i64> = Vec::new();
    let mut z: i64 = 0;
    while z < 200 {
        choose.push(0);
        z += 1;
    }

    let mut a: i64 = 0;
    while a < 20 {
        let mut b: i64 = 0;
        while b < 10 {
            if b == 0 {
                choose[(a * 10 + b) as usize] = 1;
            } else if b > a {
                choose[(a * 10 + b) as usize] = 0;
            } else if b == a {
                choose[(a * 10 + b) as usize] = 1;
            } else {
                let left = choose[((a - 1) * 10 + (b - 1)) as usize];
                let right = choose[((a - 1) * 10 + b) as usize];
                choose[(a * 10 + b) as usize] = left + right;
            }
            b += 1;
        }
        a += 1;
    }

    let h = (n + 1) / 2;
    let odd = n % 2 == 1;

    // Number of possible digit-count vectors for the half is C(h + 9, 9).
    let total_half = choose[((h + 9) * 10 + 9) as usize];
    let mut vis_size = total_half;
    if odd {
        vis_size = vis_size * 10;
    }

    let mut visited: Vec<bool> = Vec::new();
    let mut vi: i64 = 0;
    while vi < vis_size {
        visited.push(false);
        vi += 1;
    }

    let mut cnt: Vec<i64> = Vec::new();
    let mut ci: i64 = 0;
    while ci < 10 {
        cnt.push(0);
        ci += 1;
    }

    let start = p10[(h - 1) as usize];
    let end = p10[h as usize];

    let mut ans: i64 = 0;
    let mut half: i64 = start;

    while half < end {
        let mut r: i64 = 0;
        while r < 10 {
            cnt[r as usize] = 0;
            r += 1;
        }

        let middle = half % 10;

        let mut t = half;
        while t > 0 {
            let d = t % 10;
            cnt[d as usize] = cnt[d as usize] + 1;
            t = t / 10;
        }

        let mut ok = true;

        if k != 1 {
            let mut x: i64 = 0;

            if odd {
                let mut u = half / 10;
                let mut rev: i64 = 0;
                while u > 0 {
                    rev = rev * 10 + (u % 10);
                    u = u / 10;
                }
                x = half * p10[(h - 1) as usize] + rev;
            } else {
                let mut u = half;
                let mut rev: i64 = 0;
                while u > 0 {
                    rev = rev * 10 + (u % 10);
                    u = u / 10;
                }
                x = half * p10[h as usize] + rev;
            }

            ok = x % k == 0;
        }

        if ok {
            let rnk = composition_rank(&cnt, h, &choose);
            let mut idx_i = rnk;
            if odd {
                idx_i = idx_i * 10 + middle;
            }

            let idx = idx_i as usize;
            if idx < visited.len() && !visited[idx] {
                visited[idx] = true;

                let mut ways = fact[n as usize];
                let mut d: i64 = 0;

                while d < 10 {
                    let mut c = cnt[d as usize] * 2;
                    if odd && d == middle {
                        c = c - 1;
                    }
                    ways = ways / fact[c as usize];
                    d += 1;
                }

                let mut c0 = cnt[0] * 2;
                if odd && middle == 0 {
                    c0 = c0 - 1;
                }

                if c0 > 0 {
                    let no_lead_zero = ways * c0 / n;
                    ways = ways - no_lead_zero;
                }

                ans = ans + ways;
            }
        }

        half += 1;
    }

    ans
}
