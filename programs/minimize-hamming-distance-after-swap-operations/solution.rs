fn find(parent: &mut Vec<i64>, mut x: i64) -> i64 {
    while parent[x as usize] != x {
        let p = parent[x as usize];
        let gp = parent[p as usize];
        parent[x as usize] = gp;
        x = gp;
    }
    x
}

fn union(parent: &mut Vec<i64>, rank: &mut Vec<i64>, a: i64, b: i64) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra == rb {
        return;
    }

    let ra_idx = ra as usize;
    let rb_idx = rb as usize;

    if rank[ra_idx] < rank[rb_idx] {
        parent[ra_idx] = rb;
    } else if rank[ra_idx] > rank[rb_idx] {
        parent[rb_idx] = ra;
    } else {
        parent[rb_idx] = ra;
        rank[ra_idx] += 1;
    }
}

pub fn minimum_hamming_distance(
    source: &[i64],
    target: &[i64],
    allowedSwaps: &[Vec<i64>],
) -> i64 {
    let n = source.len();

    let mut parent: Vec<i64> = Vec::new();
    let mut rank: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        parent.push(i as i64);
        rank.push(0);
        i += 1;
    }

    let mut s: usize = 0;
    while s < allowedSwaps.len() {
        let a = allowedSwaps[s][0];
        let b = allowedSwaps[s][1];
        union(&mut parent, &mut rank, a, b);
        s += 1;
    }

    let mut head: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        head.push(-1);
        next.push(-1);
        i += 1;
    }

    i = 0;
    while i < n {
        let r = find(&mut parent, i as i64);
        let ri = r as usize;
        next[i] = head[ri];
        head[ri] = i as i64;
        i += 1;
    }

    let mut max_val: i64 = 0;
    i = 0;
    while i < n {
        if source[i] > max_val {
            max_val = source[i];
        }
        if target[i] > max_val {
            max_val = target[i];
        }
        i += 1;
    }

    let mut freq_s: Vec<i64> = Vec::new();
    let mut freq_t: Vec<i64> = Vec::new();

    let mut k: i64 = 0;
    while k <= max_val {
        freq_s.push(0);
        freq_t.push(0);
        k += 1;
    }

    let mut ans: i64 = 0;

    let mut r: usize = 0;
    while r < n {
        let start = head[r];
        if start != -1 {
            let mut comp_size: i64 = 0;

            let mut p = start;
            while p != -1 {
                let idx = p as usize;
                let sv = source[idx] as usize;
                let tv = target[idx] as usize;

                freq_s[sv] += 1;
                freq_t[tv] += 1;
                comp_size += 1;

                p = next[idx];
            }

            let mut matched: i64 = 0;

            p = start;
            while p != -1 {
                let idx = p as usize;

                let sv = source[idx] as usize;
                if freq_s[sv] != 0 || freq_t[sv] != 0 {
                    let a = freq_s[sv];
                    let b = freq_t[sv];
                    if a < b {
                        matched += a;
                    } else {
                        matched += b;
                    }
                    freq_s[sv] = 0;
                    freq_t[sv] = 0;
                }

                let tv = target[idx] as usize;
                if freq_s[tv] != 0 || freq_t[tv] != 0 {
                    let a = freq_s[tv];
                    let b = freq_t[tv];
                    if a < b {
                        matched += a;
                    } else {
                        matched += b;
                    }
                    freq_s[tv] = 0;
                    freq_t[tv] = 0;
                }

                p = next[idx];
            }

            ans += comp_size - matched;
        }

        r += 1;
    }

    ans
}
