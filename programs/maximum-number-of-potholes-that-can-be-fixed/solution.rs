pub fn max_potholes(road: &[u8], budget: i64) -> i64 {
    let n = road.len();

    // counts[len] = number of maximal consecutive runs of 'x' of that length.
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        counts.push(0);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < n {
        if road[idx] == b'x' {
            let mut j: usize = idx;
            while j < n && road[j] == b'x' {
                j += 1;
            }
            let len: usize = j - idx;
            counts[len] = counts[len] + 1;
            idx = j;
        } else {
            idx += 1;
        }
    }

    let mut ans: i64 = 0;
    let mut rem: i64 = budget;
    let mut done: bool = false;

    // Process runs from longest to shortest (counts indexed by length).
    let mut length: usize = n;
    while length > 0 && !done {
        let mut c: i64 = counts[length];
        let l_i: i64 = length as i64;
        while c > 0 && !done {
            if rem < 2 {
                done = true;
            } else if rem >= l_i + 1 {
                ans = ans + l_i;
                rem = rem - l_i - 1;
                c = c - 1;
            } else {
                // Cannot fully fix this run; spend the rest here partially.
                ans = ans + rem - 1;
                done = true;
            }
        }
        length -= 1;
    }

    ans
}
