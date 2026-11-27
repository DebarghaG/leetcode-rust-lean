fn collect_levels(t: &Tree, depth: usize, levels: &mut Vec<Vec<i64>>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            if depth == levels.len() {
                levels.push(Vec::new());
            }
            levels[depth].push(*v);
            collect_levels(&**l, depth + 1, levels);
            collect_levels(&**r, depth + 1, levels);
        }
    }
}

fn find_pos(sorted: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = sorted.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if sorted[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn min_swaps_for_level(level: &[i64]) -> i64 {
    let n = level.len();
    if n <= 1 {
        return 0;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        sorted.push(level[i]);
        i += 1;
    }
    sorted.sort();

    let mut perm: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let pos = find_pos(&sorted, level[i]);
        perm.push(pos as i64);
        i += 1;
    }

    let mut visited: Vec<bool> = Vec::new();
    i = 0;
    while i < n {
        visited.push(false);
        i += 1;
    }

    let mut cycles: i64 = 0;
    i = 0;
    while i < n {
        if !visited[i] {
            cycles += 1;
            let mut j = i;
            while !visited[j] {
                visited[j] = true;
                j = perm[j] as usize;
            }
        }
        i += 1;
    }

    (n as i64) - cycles
}

pub fn minimum_operations(root: &Tree) -> i64 {
    let mut levels: Vec<Vec<i64>> = Vec::new();
    collect_levels(root, 0, &mut levels);

    let mut ans: i64 = 0;
    let mut i = 0;
    while i < levels.len() {
        ans += min_swaps_for_level(&levels[i]);
        i += 1;
    }

    ans
}
