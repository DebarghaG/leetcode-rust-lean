pub fn equal_count_substrings(s: &[u8], count: i64) -> i64 {
    let n: usize = s.len();

    if n == 0 || count <= 0 {
        return 0;
    }

    let c: usize = count as usize;
    if c > n {
        return 0;
    }

    let mut max_k: usize = n / c;
    if max_k > 26 {
        max_k = 26;
    }

    let mut ans: i64 = 0;
    let count_i: i64 = count;
    let count_minus: i64 = count - 1;
    let count_plus: i64 = count + 1;

    let mut k: usize = 1;
    while k <= max_k {
        let k_i: i64 = k as i64;
        let len: usize = k * c;

        let mut freq: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < 26 {
            freq.push(0);
            z += 1;
        }

        let mut eq: i64 = 0;

        let mut i: usize = 0;
        while i < len {
            let idx: usize = (s[i] - b'a') as usize;
            let old: i64 = freq[idx];

            if old == count_minus {
                eq += 1;
            }
            if old == count_i {
                eq -= 1;
            }

            freq[idx] = old + 1;
            i += 1;
        }

        if eq == k_i {
            ans += 1;
        }

        let mut start: usize = 1;
        while start + len <= n {
            let rem_idx: usize = (s[start - 1] - b'a') as usize;
            let old_rem: i64 = freq[rem_idx];

            if old_rem == count_i {
                eq -= 1;
            }
            if old_rem == count_plus {
                eq += 1;
            }

            freq[rem_idx] = old_rem - 1;

            let add_pos: usize = start + len - 1;
            let add_idx: usize = (s[add_pos] - b'a') as usize;
            let old_add: i64 = freq[add_idx];

            if old_add == count_minus {
                eq += 1;
            }
            if old_add == count_i {
                eq -= 1;
            }

            freq[add_idx] = old_add + 1;

            if eq == k_i {
                ans += 1;
            }

            start += 1;
        }

        k += 1;
    }

    ans
}
