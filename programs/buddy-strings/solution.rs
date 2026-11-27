pub fn buddy_strings(s: &[u8], goal: &[u8]) -> bool {
    let n = s.len();
    if n != goal.len() {
        return false;
    }

    // Find the index of the first mismatch (n means "none").
    let mut first: usize = n;
    let mut i: usize = 0;
    while i < n {
        if s[i] != goal[i] && first == n {
            first = i;
        }
        i = i + 1;
    }

    // Find the index of the second mismatch (n means "none").
    let mut second: usize = n;
    let mut i2: usize = 0;
    while i2 < n {
        if s[i2] != goal[i2] && i2 != first && second == n {
            second = i2;
        }
        i2 = i2 + 1;
    }

    // Detect whether there is a third mismatch.
    let mut has_third: bool = false;
    let mut i3: usize = 0;
    while i3 < n {
        if s[i3] != goal[i3] && i3 != first && i3 != second {
            has_third = true;
        }
        i3 = i3 + 1;
    }

    if has_third {
        return false;
    }

    if second != n {
        // Exactly two mismatches: check the swap works.
        if s[first] == goal[second] {
            if s[second] == goal[first] {
                return true;
            }
        }
        return false;
    }

    if first != n {
        // Exactly one mismatch.
        return false;
    }

    // No mismatches: need at least one duplicate character to swap.
    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        counts.push(0);
        k = k + 1;
    }

    let mut j: usize = 0;
    while j < n {
        let c: usize = (s[j] - b'a') as usize;
        let v: i64 = counts[c];
        counts[c] = v + 1;
        j = j + 1;
    }

    let mut m: usize = 0;
    let mut found: bool = false;
    while m < 26 {
        if counts[m] >= 2 {
            found = true;
        }
        m = m + 1;
    }
    found
}
