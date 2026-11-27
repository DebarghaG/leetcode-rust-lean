fn find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut root = x;
    while parent[root as usize] != root {
        root = parent[root as usize];
    }

    let mut cur = x;
    while parent[cur as usize] != cur {
        let next = parent[cur as usize];
        parent[cur as usize] = root;
        cur = next;
    }

    root
}

fn union(parent: &mut Vec<i64>, size: &mut Vec<i64>, a: i64, b: i64) {
    let mut ra = find(parent, a);
    let mut rb = find(parent, b);

    if ra == rb {
        return;
    }

    if size[ra as usize] < size[rb as usize] {
        let tmp = ra;
        ra = rb;
        rb = tmp;
    }

    parent[rb as usize] = ra;
    size[ra as usize] = size[ra as usize] + size[rb as usize];
}

pub fn gcd_sort(nums: &[i64]) -> bool {
    let n = nums.len();
    if n == 0 {
        return true;
    }

    let mut max_val: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();
    let mut k: i64 = 0;
    while k <= max_val {
        parent.push(k);
        size.push(1);
        k += 1;
    }

    let mut first: Vec<i64> = Vec::new();
    k = 0;
    while k <= max_val {
        first.push(0);
        k += 1;
    }

    let mut spf: Vec<i64> = Vec::new();
    k = 0;
    while k <= max_val {
        spf.push(k);
        k += 1;
    }

    let mut p: i64 = 2;
    while p * p <= max_val {
        if spf[p as usize] == p {
            let mut q = p * p;
            while q <= max_val {
                if spf[q as usize] == q {
                    spf[q as usize] = p;
                }
                q += p;
            }
        }
        p += 1;
    }

    i = 0;
    while i < n {
        let value = nums[i];
        let mut x = value;

        while x > 1 {
            let prime = spf[x as usize];

            if first[prime as usize] == 0 {
                first[prime as usize] = value;
            } else {
                union(&mut parent, &mut size, first[prime as usize], value);
            }

            while x % prime == 0 {
                x = x / prime;
            }
        }

        i += 1;
    }

    let mut counts: Vec<i64> = Vec::new();
    k = 0;
    while k <= max_val {
        counts.push(0);
        k += 1;
    }

    i = 0;
    while i < n {
        let idx = nums[i] as usize;
        counts[idx] = counts[idx] + 1;
        i += 1;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut v: i64 = 1;
    while v <= max_val {
        while counts[v as usize] > 0 {
            sorted.push(v);
            counts[v as usize] = counts[v as usize] - 1;
        }
        v += 1;
    }

    i = 0;
    while i < n {
        let a = find(&mut parent, nums[i]);
        let b = find(&mut parent, sorted[i]);
        if a != b {
            return false;
        }
        i += 1;
    }

    true
}
