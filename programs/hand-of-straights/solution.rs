pub fn is_n_straight_hand(hand: &[i64], group_size: i64) -> bool {
    let n = hand.len();

    // Basic feasibility checks (outside of any loop, so early return is fine).
    if group_size <= 0 {
        return false;
    }
    let g = group_size as usize;
    if g > n {
        return false;
    }
    if n % g != 0 {
        return false;
    }

    // Copy the input into an owned vector.
    let mut v: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < n {
        v.push(hand[p]);
        p = p + 1;
    }

    // Manual ascending selection sort.
    let mut a: usize = 0;
    while a < n {
        let mut minidx: usize = a;
        let mut b: usize = a + 1;
        while b < n {
            if v[b] < v[minidx] {
                minidx = b;
            }
            b = b + 1;
        }
        let tmp = v[a];
        v[a] = v[minidx];
        v[minidx] = tmp;
        a = a + 1;
    }

    // Compress into distinct values (vals) with counts (freq), ascending.
    let mut vals: Vec<i64> = Vec::new();
    let mut freq: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    let mut j: usize = 0;
    while j < n {
        let x = v[j];
        let mut same = false;
        if idx > 0 {
            if vals[idx - 1] == x {
                same = true;
            }
        }
        if same {
            freq[idx - 1] = freq[idx - 1] + 1;
        } else {
            vals.push(x);
            freq.push(1);
            idx = idx + 1;
        }
        j = j + 1;
    }
    let m = idx;

    // starts[i] = number of groups whose smallest card is vals[i].
    let mut starts: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < m {
        starts.push(0);
        t = t + 1;
    }

    // Single-pass feasibility computation, using a flag instead of early return.
    let mut ok = true;
    let mut carry: i64 = 0;
    let mut i: usize = 0;
    while i < m && ok {
        let s = freq[i] - carry;
        if s < 0 {
            ok = false;
        } else {
            starts[i] = s;
            let reach_i = freq[i];

            // Groups that started at i+1-g complete exactly at position i.
            let mut ended: i64 = 0;
            if i + 1 >= g {
                ended = starts[i + 1 - g];
            }

            if i + 1 < m {
                let mut consec = false;
                if vals[i + 1] == vals[i] + 1 {
                    consec = true;
                }
                if consec {
                    carry = reach_i - ended;
                } else {
                    if reach_i - ended != 0 {
                        ok = false;
                    }
                    carry = 0;
                }
            } else {
                if reach_i - ended != 0 {
                    ok = false;
                }
            }
        }
        i = i + 1;
    }

    ok
}
