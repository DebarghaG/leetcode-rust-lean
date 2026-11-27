pub fn can_transform(start: &[u8], result: &[u8]) -> bool {
    if start.len() != result.len() {
        return false;
    }
    let n: usize = start.len();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < n || j < n {
        // advance i to the next non-'X' byte in start
        while i < n && start[i] == b'X' {
            i += 1;
        }
        // advance j to the next non-'X' byte in result
        while j < n && result[j] == b'X' {
            j += 1;
        }

        let i_end: bool = i >= n;
        let j_end: bool = j >= n;
        if i_end || j_end {
            return i_end && j_end;
        }

        // the non-'X' characters must match
        if start[i] != result[j] {
            return false;
        }

        // 'L' can only move left, so its start index must be >= result index
        if start[i] == b'L' && i < j {
            return false;
        }

        // 'R' can only move right, so its start index must be <= result index
        if start[i] == b'R' && i > j {
            return false;
        }

        i += 1;
        j += 1;
    }
    true
}
