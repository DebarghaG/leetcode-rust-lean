pub fn minimum_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut max_v: i64 = nums[0];
    let mut i: usize = 1;
    while i < n {
        if nums[i] > max_v {
            max_v = nums[i];
        }
        i += 1;
    }

    let size: usize = (max_v + 1) as usize;
    let mut freq_even: Vec<i64> = Vec::new();
    let mut freq_odd: Vec<i64> = Vec::new();

    let mut t: usize = 0;
    while t < size {
        freq_even.push(0);
        freq_odd.push(0);
        t += 1;
    }

    let mut idx: usize = 0;
    while idx < n {
        let v: usize = nums[idx] as usize;
        if idx % 2 == 0 {
            freq_even[v] = freq_even[v] + 1;
        } else {
            freq_odd[v] = freq_odd[v] + 1;
        }
        idx += 1;
    }

    let even_len: i64 = ((n + 1) / 2) as i64;
    let odd_len: i64 = (n / 2) as i64;

    let mut e1v: i64 = -1;
    let mut e1c: i64 = 0;
    let mut e2v: i64 = -2;
    let mut e2c: i64 = 0;

    let mut v: usize = 0;
    while v < size {
        let c: i64 = freq_even[v];
        if c > 0 {
            if c > e1c {
                e2v = e1v;
                e2c = e1c;
                e1v = v as i64;
                e1c = c;
            } else if c > e2c && (v as i64) != e1v {
                e2v = v as i64;
                e2c = c;
            }
        }
        v += 1;
    }

    let mut o1v: i64 = -1;
    let mut o1c: i64 = 0;
    let mut o2v: i64 = -2;
    let mut o2c: i64 = 0;

    v = 0;
    while v < size {
        let c: i64 = freq_odd[v];
        if c > 0 {
            if c > o1c {
                o2v = o1v;
                o2c = o1c;
                o1v = v as i64;
                o1c = c;
            } else if c > o2c && (v as i64) != o1v {
                o2v = v as i64;
                o2c = c;
            }
        }
        v += 1;
    }

    if odd_len == 0 {
        return even_len - e1c;
    }

    let mut best: i64 = even_len + odd_len;

    if e1v != o1v {
        let cost = (even_len - e1c) + (odd_len - o1c);
        if cost < best {
            best = cost;
        }
    } else {
        let cost1 = (even_len - e1c) + (odd_len - o2c);
        if cost1 < best {
            best = cost1;
        }

        let cost2 = (even_len - e2c) + (odd_len - o1c);
        if cost2 < best {
            best = cost2;
        }
    }

    best
}
