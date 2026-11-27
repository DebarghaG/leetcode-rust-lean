fn radix_pass(src: &[i64], dst: &mut Vec<i64>, shift: usize) {
    let n: usize = src.len();

    let mut count: Vec<i64> = Vec::new();
    let mut b: usize = 0;
    while b < 512 {
        count.push(0);
        b += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let key: i64 = src[i];
        let pos: i64 = key >> 32;
        let bucket_i: i64 = (pos >> shift) & 511;
        let bucket: usize = bucket_i as usize;
        count[bucket] = count[bucket] + 1;
        i += 1;
    }

    let mut sum: i64 = 0;
    b = 0;
    while b < 512 {
        let c: i64 = count[b];
        count[b] = sum;
        sum = sum + c;
        b += 1;
    }

    i = 0;
    while i < n {
        let key: i64 = src[i];
        let pos: i64 = key >> 32;
        let bucket_i: i64 = (pos >> shift) & 511;
        let bucket: usize = bucket_i as usize;
        let dest_i: i64 = count[bucket];
        let dest: usize = dest_i as usize;
        dst[dest] = key;
        count[bucket] = count[bucket] + 1;
        i += 1;
    }
}

fn radix_sort_events(v: &mut Vec<i64>) {
    let n: usize = v.len();
    if n < 2 {
        return;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    radix_pass(&v[..], &mut tmp, 0);
    radix_pass(&tmp[..], v, 9);
}

pub fn split_painting(segments: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n: usize = segments.len();
    let offset: i64 = 1000000000;
    let mut events: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let seg = &segments[i];
        let s: i64 = seg[0];
        let e: i64 = seg[1];
        let c: i64 = seg[2];

        let start_key: i64 = (s << 32) + (c + offset);
        let end_key: i64 = (e << 32) + (-c + offset);

        events.push(start_key);
        events.push(end_key);
        i += 1;
    }

    radix_sort_events(&mut events);

    let mut out: Vec<Vec<i64>> = Vec::new();
    let len: usize = events.len();
    let mask: i64 = 4294967295;
    let mut idx: usize = 0;
    let mut cur: i64 = 0;
    let mut prev: i64 = 0;

    while idx < len {
        let key0: i64 = events[idx];
        let p: i64 = key0 >> 32;

        if p > prev {
            if cur > 0 {
                let mut row: Vec<i64> = Vec::new();
                row.push(prev);
                row.push(p);
                row.push(cur);
                out.push(row);
            }
        }

        let limit: i64 = (p + 1) << 32;
        let mut delta_sum: i64 = 0;
        while idx < len {
            let key: i64 = events[idx];
            if key >= limit {
                break;
            }
            let val: i64 = key & mask;
            let d: i64 = val - offset;
            delta_sum = delta_sum + d;
            idx += 1;
        }

        cur = cur + delta_sum;
        prev = p;
    }

    out
}
