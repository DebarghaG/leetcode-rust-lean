pub fn longest_beautiful_substring(word: &[u8]) -> i64 {
    let n = word.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let seg_start = i;
        let mut j = i + 1;

        while j < n {
            if word[j] >= word[j - 1] {
                j += 1;
            } else {
                break;
            }
        }

        let mut has_a = false;
        let mut has_e = false;
        let mut has_i = false;
        let mut has_o = false;
        let mut has_u = false;

        let mut first_a: i64 = -1;
        let mut last_u: i64 = -1;

        let mut k = seg_start;
        while k < j {
            let b = word[k];

            if b == b'a' {
                has_a = true;
                if first_a < 0 {
                    first_a = k as i64;
                }
            } else if b == b'e' {
                has_e = true;
            } else if b == b'i' {
                has_i = true;
            } else if b == b'o' {
                has_o = true;
            } else {
                has_u = true;
                last_u = k as i64;
            }

            k += 1;
        }

        if has_a && has_e && has_i && has_o && has_u && first_a >= 0 && last_u >= 0 {
            let len = last_u - first_a + 1;
            if len > ans {
                ans = len;
            }
        }

        i = j;
    }

    ans
}
