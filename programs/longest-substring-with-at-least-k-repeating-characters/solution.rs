pub fn longest_substring(s: &[u8], k: i64) -> i64 {
    let n: usize = s.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 0;
    let mut target_distinct: i64 = 1;

    while target_distinct <= 26 {
        let mut counts: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < 26 {
            counts.push(0);
            i += 1;
        }

        let mut left: usize = 0;
        let mut right: usize = 0;
        let mut unique: i64 = 0;
        let mut at_least_k: i64 = 0;

        while right < n {
            let idx: usize = (s[right] as usize) - 97;
            counts[idx] += 1;

            if counts[idx] == 1 {
                unique += 1;
            }
            if counts[idx] == k {
                at_least_k += 1;
            }

            while unique > target_distinct {
                let left_idx: usize = (s[left] as usize) - 97;

                if counts[left_idx] == k {
                    at_least_k -= 1;
                }

                counts[left_idx] -= 1;

                if counts[left_idx] == 0 {
                    unique -= 1;
                }

                left += 1;
            }

            if unique == target_distinct && at_least_k == target_distinct {
                let len: i64 = (right - left + 1) as i64;
                if len > best {
                    best = len;
                }
            }

            right += 1;
        }

        target_distinct += 1;
    }

    best
}
