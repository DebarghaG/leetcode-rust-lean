pub fn count_palindrome_paths(parent: &[i64], s: &[u8]) -> i64 {
    let n = parent.len();
    if n == 0 {
        return 0;
    }

    let mut first: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();
    let mut masks: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        first.push(-1);
        next.push(-1);
        masks.push(0);
        i += 1;
    }

    i = 1;
    while i < n {
        let p = parent[i] as usize;
        next[i] = first[p];
        first[p] = i as i64;
        i += 1;
    }

    let mut table_size: usize = 1;
    let target_size = 2 * n + 1;
    while table_size < target_size {
        table_size = table_size * 2;
    }
    let table_mask: i64 = table_size as i64 - 1;

    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    i = 0;
    while i < table_size {
        keys.push(-1);
        counts.push(0);
        i += 1;
    }

    let mut answer: i64 = 0;
    let mut queue: Vec<i64> = Vec::new();
    queue.push(0);
    let mut head: usize = 0;

    while head < queue.len() {
        let u = queue[head] as usize;
        head += 1;
        let m = masks[u];

        answer += map_get(&keys, &counts, table_size, m);

        let mut b: i64 = 0;
        while b < 26 {
            let target = m ^ (1i64 << b);
            answer += map_get(&keys, &counts, table_size, target);
            b += 1;
        }

        let mut idx: usize = (((m * 2654435761i64) & table_mask) as usize);
        let mut steps: usize = 0;
        let mut inserted: bool = false;
        while steps < table_size && !inserted {
            let k = keys[idx];
            if k == -1 {
                keys[idx] = m;
                counts[idx] = 1;
                inserted = true;
            } else if k == m {
                counts[idx] = counts[idx] + 1;
                inserted = true;
            } else {
                idx = (idx + 1) & (table_size - 1);
                steps += 1;
            }
        }

        let mut child = first[u];
        while child != -1 {
            let v = child as usize;
            let c = s[v] as i64 - 97i64;
            let bit = 1i64 << c;
            masks[v] = m ^ bit;
            queue.push(v as i64);
            child = next[v];
        }
    }

    answer
}

fn map_get(keys: &[i64], counts: &[i64], table_size: usize, key: i64) -> i64 {
    let table_mask: i64 = table_size as i64 - 1;
    let mut idx: usize = (((key * 2654435761i64) & table_mask) as usize);
    let mut steps: usize = 0;

    while steps < table_size {
        let k = keys[idx];
        if k == -1 {
            return 0;
        }
        if k == key {
            return counts[idx];
        }
        idx = (idx + 1) & (table_size - 1);
        steps += 1;
    }

    0
}
