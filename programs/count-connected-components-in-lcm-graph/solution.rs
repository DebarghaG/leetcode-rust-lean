fn find(parent: &mut Vec<i64>, mut x: i64) -> i64 {
    let mut root = x;
    while parent[root as usize] != root {
        root = parent[root as usize];
    }

    while parent[x as usize] != x {
        let p = parent[x as usize];
        parent[x as usize] = root;
        x = p;
    }

    root
}

fn dsu_union(parent: &mut Vec<i64>, rank: &mut Vec<i64>, a: i64, b: i64) {
    let ra = find(parent, a);
    let rb = find(parent, b);

    if ra != rb {
        let ra_idx = ra as usize;
        let rb_idx = rb as usize;

        if rank[ra_idx] < rank[rb_idx] {
            parent[ra_idx] = rb;
        } else if rank[ra_idx] > rank[rb_idx] {
            parent[rb_idx] = ra;
        } else {
            parent[rb_idx] = ra;
            rank[ra_idx] = rank[ra_idx] + 1;
        }
    }
}

pub fn count_components(nums: &[i64], threshold: i64) -> i64 {
    let n = nums.len();
    let t = threshold as usize;

    let mut present: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i <= t {
        present.push(false);
        i += 1;
    }

    let mut isolated: i64 = 0;
    i = 0;
    while i < n {
        let v = nums[i];
        if v <= threshold {
            present[v as usize] = true;
        } else {
            isolated += 1;
        }
        i += 1;
    }

    let mut value_index: Vec<i64> = Vec::new();
    i = 0;
    while i <= t {
        value_index.push(-1);
        i += 1;
    }

    let mut idx: i64 = 0;
    let mut v: usize = 1;
    while v <= t {
        if present[v] {
            value_index[v] = idx;
            idx += 1;
        }
        v += 1;
    }

    let actual_nodes = idx as usize;

    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < actual_nodes {
        parent.push(i as i64);
        i += 1;
    }

    let mut rank: Vec<i64> = Vec::new();
    i = 0;
    while i < actual_nodes {
        rank.push(0);
        i += 1;
    }

    let mut first_div: Vec<i64> = Vec::new();
    i = 0;
    while i <= t {
        first_div.push(-1);
        i += 1;
    }

    let mut x: usize = 1;
    while x <= t {
        if present[x] {
            let node_x = value_index[x];
            let mut m: usize = x;

            while m <= t {
                if first_div[m] == -1 {
                    first_div[m] = node_x;
                } else {
                    let other = first_div[m];
                    dsu_union(&mut parent, &mut rank, node_x, other);
                }
                m += x;
            }
        }
        x += 1;
    }

    let mut seen: Vec<bool> = Vec::new();
    i = 0;
    while i < actual_nodes {
        seen.push(false);
        i += 1;
    }

    let mut components: i64 = 0;
    let mut j: i64 = 0;
    while j < idx {
        let r = find(&mut parent, j);
        let ri = r as usize;
        if !seen[ri] {
            seen[ri] = true;
            components += 1;
        }
        j += 1;
    }

    components + isolated
}
