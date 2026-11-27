pub fn count_prefix_suffix_pairs(words: &[Vec<u8>]) -> i64 {
    let n: usize = words.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;

        while j < n {
            let a_len: usize = words[i].len();
            let b_len: usize = words[j].len();

            if a_len <= b_len {
                let mut ok: bool = true;
                let mut k: usize = 0;

                while k < a_len {
                    if words[i][k] != words[j][k] {
                        ok = false;
                    }
                    if words[i][k] != words[j][b_len - a_len + k] {
                        ok = false;
                    }
                    k += 1;
                }

                if ok {
                    ans += 1;
                }
            }

            j += 1;
        }

        i += 1;
    }

    ans
}
