pub fn frequencies_of_elements(head: &List) -> List {
    let mut vals: Vec<i64> = Vec::new();
    let mut cur: &List = head;
    let mut done = false;

    while !done {
        match cur {
            List::Nil => {
                done = true;
            }
            List::Cons(v, next) => {
                vals.push(*v);
                cur = &**next;
            }
        }
    }

    let n = vals.len();
    let n_i64 = n as i64;

    // Flat hash-table buckets: each bucket stores the head id of a chain.
    let mut bucket_head: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        bucket_head.push(-1);
        i = i + 1;
    }

    let mut distinct_values: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    let mut seen: Vec<i64> = Vec::new();
    let mut next_id: Vec<i64> = Vec::new();
    let mut ids: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        let val = vals[i];
        let b = (val % n_i64) as usize;

        let mut cur_id = bucket_head[b];
        let mut found: i64 = -1;

        while cur_id >= 0 {
            let id = cur_id as usize;
            if distinct_values[id] == val {
                found = cur_id;
            }
            cur_id = next_id[id];
        }

        if found >= 0 {
            let id = found as usize;
            counts[id] = counts[id] + 1;
            ids.push(found);
        } else {
            let id = distinct_values.len();

            distinct_values.push(val);
            counts.push(1);
            seen.push(0);

            next_id.push(bucket_head[b]);
            bucket_head[b] = id as i64;

            ids.push(id as i64);
        }

        i = i + 1;
    }

    // Prepend frequencies in first-occurrence order, which reverses them.
    let mut result: List = List::Nil;
    i = 0;
    while i < n {
        let id = ids[i] as usize;
        if seen[id] == 0 {
            seen[id] = 1;
            result = List::Cons(counts[id], Box::new(result));
        }
        i = i + 1;
    }

    result
}
