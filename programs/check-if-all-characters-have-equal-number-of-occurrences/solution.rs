pub fn are_occurrences_equal(s: &[u8]) -> bool {
    // Count occurrences per byte value (256 slots, no underflow risk).
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 256 {
        counts.push(0);
        i += 1;
    }

    let mut j: usize = 0;
    while j < s.len() {
        let idx: usize = s[j] as usize;
        counts[idx] = counts[idx] + 1;
        j += 1;
    }

    // Find the first character that actually occurs, then require every
    // other occurring character to have that same frequency.
    let mut target: i64 = -1;
    let mut k: usize = 0;
    while k < 256 {
        if counts[k] > 0 {
            if target == -1 {
                target = counts[k];
            } else if counts[k] != target {
                return false;
            }
        }
        k += 1;
    }

    // No character occurred at all (empty string): not a "good" string.
    if target == -1 {
        return false;
    }

    true
}
