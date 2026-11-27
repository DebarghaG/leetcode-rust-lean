pub fn shortest_way(source: &[u8], target: &[u8]) -> i64 {
    let n: usize = target.len();
    if n == 0 {
        return 0;
    }

    let m: usize = source.len();
    if m == 0 {
        return -1;
    }

    // First check that every character in target occurs somewhere in source.
    let mut k: usize = 0;
    while k < n {
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < m {
            if source[j] == target[k] {
                found = true;
            }
            j += 1;
        }
        if !found {
            return -1;
        }
        k += 1;
    }

    // Greedily consume as much of target as possible in each pass over source.
    let mut count: i64 = 1;
    let mut i: usize = 0; // index in target
    let mut j: usize = 0; // index in source

    while i < n {
        while j < m && i < n {
            if source[j] == target[i] {
                i += 1;
            }
            j += 1;
        }

        if i < n {
            count += 1;
            j = 0;
        }
    }

    count
}
