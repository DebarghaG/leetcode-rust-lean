pub fn find_valid_split(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return -1;
    }

    // Build primes up to 1000 using a small sieve.
    let limit: usize = 1000;
    let mut is_comp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t <= limit {
        is_comp.push(0);
        t += 1;
    }

    let mut p: usize = 2;
    while p * p <= limit {
        if is_comp[p] == 0 {
            let mut m: usize = p * p;
            while m <= limit {
                is_comp[m] = 1;
                m += p;
            }
        }
        p += 1;
    }

    let mut primes: Vec<i64> = Vec::new();
    let mut q: usize = 2;
    while q <= limit {
        if is_comp[q] == 0 {
            primes.push(q as i64);
        }
        q += 1;
    }

    // Hash table for prime -> (first_position, last_position).
    // Size is based on n, not on the maximum value in nums.
    let mut cap: usize = 64;
    let target: usize = 16 * n;
    while cap < target {
        cap = cap * 2;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < cap {
        keys.push(-1);
        vals.push(-1);
        idx += 1;
    }

    let base: i64 = n as i64;

    let mut i: usize = 0;
    while i < n {
        let pos: i64 = i as i64;
        let mut x: i64 = nums[i];
        let mut pi: usize = 0;
        let mut factor_done: bool = false;

        while pi < primes.len() && !factor_done {
            let pp: i64 = primes[pi];
            if pp * pp > x {
                factor_done = true;
            } else {
                if x % pp == 0 {
                    let mut h: usize = ((pp * 1000003) % (cap as i64)) as usize;
                    let mut done: bool = false;
                    while !done {
                        let k = keys[h];
                        if k == pp {
                            let old = vals[h];
                            let first = old / base;
                            vals[h] = first * base + pos;
                            done = true;
                        } else if k == -1 {
                            keys[h] = pp;
                            vals[h] = pos * base + pos;
                            done = true;
                        } else {
                            h += 1;
                            if h == cap {
                                h = 0;
                            }
                        }
                    }

                    while x % pp == 0 {
                        x = x / pp;
                    }
                }
                pi += 1;
            }
        }

        if x > 1 {
            let pp: i64 = x;
            let mut h: usize = ((pp * 1000003) % (cap as i64)) as usize;
            let mut done: bool = false;
            while !done {
                let k = keys[h];
                if k == pp {
                    let old = vals[h];
                    let first = old / base;
                    vals[h] = first * base + pos;
                    done = true;
                } else if k == -1 {
                    keys[h] = pp;
                    vals[h] = pos * base + pos;
                    done = true;
                } else {
                    h += 1;
                    if h == cap {
                        h = 0;
                    }
                }
            }
        }

        i += 1;
    }

    // For every prime appearing at first..last, splits i with
    // first <= i < last are invalid.
    let mut diff: Vec<i64> = Vec::new();
    let mut d: usize = 0;
    while d <= n {
        diff.push(0);
        d += 1;
    }

    let mut s: usize = 0;
    while s < cap {
        let k = keys[s];
        if k != -1 {
            let v = vals[s];
            let first = v / base;
            let last = v % base;
            if first < last {
                diff[first as usize] += 1;
                diff[last as usize] -= 1;
            }
        }
        s += 1;
    }

    let mut cur: i64 = 0;
    i = 0;
    while i + 1 < n {
        cur += diff[i];
        if cur == 0 {
            return i as i64;
        }
        i += 1;
    }

    -1
}
