pub fn maximum_subsequence_count(text: &[u8], pattern: &[u8]) -> i64 {
    let a = pattern[0];
    let b = pattern[1];

    if a == b {
        let mut count: i64 = 0;
        let mut i: usize = 0;
        while i < text.len() {
            if text[i] == a {
                count += 1;
            }
            i += 1;
        }
        return count * (count + 1) / 2;
    }

    let mut count_a: i64 = 0;
    let mut count_b: i64 = 0;
    let mut base: i64 = 0;

    let mut i: usize = 0;
    while i < text.len() {
        let c = text[i];

        if c == a {
            count_a += 1;
        }

        if c == b {
            count_b += 1;
            base += count_a;
        }

        i += 1;
    }

    let extra = if count_a > count_b { count_a } else { count_b };
    base + extra
}
