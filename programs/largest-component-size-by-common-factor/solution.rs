fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut r: usize = x as usize;
    while parent[r] >= 0 {
        r = parent[r] as usize;
    }

    let mut cur: usize = x as usize;
    while parent[cur] >= 0 {
        let nxt: usize = parent[cur] as usize;
        parent[cur] = r as i64;
        cur = nxt;
    }

    r as i64
}

fn union_sets(parent: &mut Vec<i64>, a: i64, b: i64) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra == rb {
        return;
    }

    let ua = ra as usize;
    let ub = rb as usize;
    let sa = parent[ua];
    let sb = parent[ub];

    if sa > sb {
        parent[ub] = sa + sb;
        parent[ua] = rb;
    } else {
        parent[ua] = sa + sb;
        parent[ub] = ra;
    }
}

fn add_factor(
    keys: &mut Vec<i64>,
    vals: &mut Vec<i64>,
    parent: &mut Vec<i64>,
    cap: usize,
    f: i64,
    owner: i64,
) {
    let cap_i64 = cap as i64;
    let mut h: usize = (f % cap_i64) as usize;

    while keys[h] != -1 && keys[h] != f {
        h += 1;
        if h == cap {
            h = 0;
        }
    }

    if keys[h] == -1 {
        keys[h] = f;
        vals[h] = owner;
    } else {
        let other = vals[h];
        union_sets(parent, owner, other);
    }
}

pub fn largest_component_size(nums: &[i64]) -> i64 {
    let n_usize = nums.len();
    if n_usize == 0 {
        return 0;
    }

    let mut primes: Vec<i64> = Vec::new();
    let mut p: i64 = 2;
    while p <= 316 {
        let mut is_prime: bool = true;
        let mut d: i64 = 2;
        while d * d <= p {
            if p % d == 0 {
                is_prime = false;
                d = p;
            } else {
                d += 1;
            }
        }
        if is_prime {
            primes.push(p);
        }
        p += 1;
    }

    let mut maxv = nums[0];
    let mut idx: usize = 1;
    while idx < n_usize {
        if nums[idx] > maxv {
            maxv = nums[idx];
        }
        idx += 1;
    }

    let mut bound: i64 = 6 * (n_usize as i64);
    if maxv < bound {
        bound = maxv;
    }
    if bound > 10000 {
        bound = 10000;
    }
    if bound < 1 {
        bound = 1;
    }

    let mut target: usize = (bound as usize) * 2;
    if target < 8 {
        target = 8;
    }
    let mut cap: usize = target;
    if cap % 2 == 0 {
        cap += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        parent.push(-1);
        i += 1;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < cap {
        keys.push(-1);
        vals.push(0);
        t += 1;
    }

    i = 0;
    while i < n_usize {
        let mut x = nums[i];
        let mut pidx: usize = 0;
        let mut stop: bool = false;

        while pidx < primes.len() && !stop {
            let pd = primes[pidx];
            if pd * pd > x {
                stop = true;
            } else {
                if x % pd == 0 {
                    add_factor(&mut keys, &mut vals, &mut parent, cap, pd, i as i64);
                    while x % pd == 0 {
                        x = x / pd;
                    }
                }
                pidx += 1;
            }
        }

        if x > 1 {
            add_factor(&mut keys, &mut vals, &mut parent, cap, x, i as i64);
        }

        i += 1;
    }

    let mut best: i64 = 0;
    let mut r: usize = 0;
    while r < n_usize {
        if parent[r] < 0 {
            let s = -parent[r];
            if s > best {
                best = s;
            }
        }
        r += 1;
    }

    best
}
