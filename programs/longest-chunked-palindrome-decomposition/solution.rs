pub fn longest_decomposition(text: &[u8]) -> i64 {
    let n = text.len();
    let mut left: usize = 0;
    let mut right: usize = n;
    let mut ans: i64 = 0;

    while left < right {
        let rem = right - left;
        let max_len = rem / 2;
        let mut split: usize = 0;
        let mut l: usize = 1;

        while l <= max_len {
            let mut ok: bool = true;
            let mut i: usize = 0;

            while i < l {
                if text[left + i] != text[right - l + i] {
                    ok = false;
                    break;
                }
                i += 1;
            }

            if ok {
                split = l;
                break;
            }

            l += 1;
        }

        if split == 0 {
            ans += 1;
            break;
        } else {
            ans += 2;
            left += split;
            right -= split;
        }
    }

    ans
}
