pub fn max_number_of_balloons(text: &[u8]) -> i64 {
    let mut count_b: i64 = 0;
    let mut count_a: i64 = 0;
    let mut count_l: i64 = 0;
    let mut count_o: i64 = 0;
    let mut count_n: i64 = 0;

    let mut i: usize = 0;
    while i < text.len() {
        let c = text[i];
        if c == b'b' {
            count_b += 1;
        } else if c == b'a' {
            count_a += 1;
        } else if c == b'l' {
            count_l += 1;
        } else if c == b'o' {
            count_o += 1;
        } else if c == b'n' {
            count_n += 1;
        }
        i += 1;
    }

    let mut ans: i64 = count_b;

    if count_a < ans {
        ans = count_a;
    }
    if count_l / 2 < ans {
        ans = count_l / 2;
    }
    if count_o / 2 < ans {
        ans = count_o / 2;
    }
    if count_n < ans {
        ans = count_n;
    }

    ans
}
