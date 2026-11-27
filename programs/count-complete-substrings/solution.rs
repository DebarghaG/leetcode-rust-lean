pub fn count_complete_substrings(word: &[u8], k: i64) -> i64 {
    let n = word.len();
    if n == 0 || k <= 0 {
        return 0;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i;

        while j + 1 < n {
            let a = word[j] as i64;
            let b = word[j + 1] as i64;
            let d = if a >= b { a - b } else { b - a };

            if d > 2 {
                break;
            }
            j += 1;
        }

        let seg_len = j - i + 1;
        let mut m: i64 = 1;

        while m <= 26 {
            let w_i64 = m * k;
            if w_i64 > seg_len as i64 {
                break;
            }

            let w = w_i64 as usize;

            let mut freq: Vec<i64> = Vec::new();
            let mut z: usize = 0;
            while z < 26 {
                freq.push(0);
                z += 1;
            }

            let mut idx: usize = i;
            while idx < i + w {
                let c = (word[idx] as i64 - 97) as usize;
                freq[c] += 1;
                idx += 1;
            }

            let mut eq: i64 = 0;
            z = 0;
            while z < 26 {
                if freq[z] == k {
                    eq += 1;
                }
                z += 1;
            }

            if eq == m {
                ans += 1;
            }

            let mut p: usize = i;
            while p + w < j + 1 {
                let old_c = (word[p] as i64 - 97) as usize;

                if freq[old_c] == k {
                    eq -= 1;
                }
                freq[old_c] -= 1;
                if freq[old_c] == k {
                    eq += 1;
                }

                let add_idx = p + w;
                let new_c = (word[add_idx] as i64 - 97) as usize;

                if freq[new_c] == k {
                    eq -= 1;
                }
                freq[new_c] += 1;
                if freq[new_c] == k {
                    eq += 1;
                }

                p += 1;

                if eq == m {
                    ans += 1;
                }
            }

            m += 1;
        }

        i = j + 1;
    }

    ans
}
