pub fn count_palindromic_subsequence(s: &[u8]) -> i64 {
    let n = s.len();
    let mut ans: i64 = 0;

    let mut a: usize = 0;
    while a < 26 {
        let target: u8 = b'a' + (a as u8);

        // First occurrence: assign at most once (guarded by sentinel n).
        let mut first: usize = n;
        let mut i: usize = 0;
        while i < n {
            if s[i] == target {
                if first == n {
                    first = i;
                }
            }
            i += 1;
        }

        // Last occurrence via reverse scan: assign at most once.
        let mut last: usize = n;
        let mut j: usize = 0;
        while j < n {
            let idx: usize = n - 1 - j;
            if s[idx] == target {
                if last == n {
                    last = idx;
                }
            }
            j += 1;
        }

        if first != n {
            if last > first {
                // Frequency table for characters strictly between first and last.
                let mut seen: Vec<i64> = Vec::new();
                let mut z: usize = 0;
                while z < 26 {
                    seen.push(0);
                    z += 1;
                }

                let mut k: usize = first + 1;
                while k < last {
                    let d: usize = (s[k] - b'a') as usize;
                    seen[d] = seen[d] + 1;
                    k += 1;
                }

                let mut d: usize = 0;
                while d < 26 {
                    if seen[d] != 0 {
                        ans += 1;
                    }
                    d += 1;
                }
            }
        }

        a += 1;
    }

    ans
}
