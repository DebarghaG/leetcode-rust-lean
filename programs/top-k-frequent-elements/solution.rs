pub fn top_k_frequent(nums: &[i64], k: i64) -> Vec<i64> {
    let n: usize = nums.len();

    // Capacity for a simple open-addressing table.
    // The value range guarantees at most 20001 distinct values.
    let mut max_unique: usize = n;
    if max_unique > 20001 {
        max_unique = 20001;
    }

    let mut cap: usize = 8;
    let target: usize = max_unique + max_unique / 2 + 1;
    while cap < target {
        cap *= 2;
    }

    let mut table: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < cap {
        table.push(0);
        t += 1;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut cnts: Vec<i64> = Vec::new();

    // Count frequencies while preserving first-occurrence order in `vals`.
    let mut i: usize = 0;
    while i < n {
        let v = nums[i];
        let mut pos: usize = ((v + 10000) as usize) & (cap - 1);
        let mut found: bool = false;

        while !found {
            let cur = table[pos];
            if cur == 0 {
                let idx = vals.len() as i64;
                table[pos] = ((v + 10000) << 20) | (idx + 1);
                vals.push(v);
                cnts.push(1);
                found = true;
            } else {
                let key = (cur >> 20) - 10000;
                if key == v {
                    let idx = ((cur & 1048575) - 1) as usize;
                    cnts[idx] = cnts[idx] + 1;
                    found = true;
                } else {
                    pos = (pos + 1) & (cap - 1);
                }
            }
        }

        i += 1;
    }

    let u: usize = vals.len();
    let mut maxfreq: i64 = 1;
    let mut j: usize = 0;
    while j < u {
        if cnts[j] > maxfreq {
            maxfreq = cnts[j];
        }
        j += 1;
    }

    let k_usize: usize = k as usize;

    // For few distinct values, a tiny insertion sort is cheap and avoids
    // allocating a frequency bucket array of size maxfreq.
    if u <= 256 {
        let mut order: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < u {
            order.push(q as i64);
            q += 1;
        }

        let mut a: usize = 1;
        while a < u {
            let cur_i64 = order[a];
            let cur_idx = cur_i64 as usize;
            let cur_cnt = cnts[cur_idx];
            let mut b: usize = a;

            while b > 0 {
                let prev_i64 = order[b - 1];
                let prev_idx = prev_i64 as usize;
                let prev_cnt = cnts[prev_idx];

                let mut swap: bool = false;
                if prev_cnt < cur_cnt {
                    swap = true;
                } else if prev_cnt == cur_cnt && prev_idx > cur_idx {
                    swap = true;
                }

                if swap {
                    order[b] = prev_i64;
                    b -= 1;
                } else {
                    break;
                }
            }

            order[b] = cur_i64;
            a += 1;
        }

        let mut result: Vec<i64> = Vec::new();
        let mut r: usize = 0;
        while r < k_usize && r < u {
            let idx = order[r] as usize;
            result.push(vals[idx]);
            r += 1;
        }
        return result;
    }

    // Bucket distinct values by frequency using linked lists.
    // Iterating backwards and prepending preserves first-occurrence order
    // inside each frequency bucket.
    let mf: usize = maxfreq as usize;
    let mut head: Vec<i64> = Vec::new();
    let mut h: usize = 0;
    while h <= mf {
        head.push(-1);
        h += 1;
    }

    let mut next: Vec<i64> = Vec::new();
    let mut t2: usize = 0;
    while t2 < u {
        next.push(-1);
        t2 += 1;
    }

    let mut i2: usize = u;
    while i2 > 0 {
        i2 -= 1;
        let c = cnts[i2] as usize;
        next[i2] = head[c];
        head[c] = i2 as i64;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut f: i64 = maxfreq;

    while f >= 1 && result.len() < k_usize {
        let fi = f as usize;
        let mut node = head[fi];

        while node != -1 && result.len() < k_usize {
            result.push(vals[node as usize]);
            node = next[node as usize];
        }

        f -= 1;
    }

    result
}
