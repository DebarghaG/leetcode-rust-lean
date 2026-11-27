fn letter_value(b: u8) -> i64 {
    let p: i64 = (b as i64) - 97 + 1;
    if p <= 2 {
        1
    } else {
        2 + (p - 3) / 3
    }
}

pub fn count_divisible_substrings(word: &[u8]) -> i64 {
    let n: usize = word.len();
    let mut ans: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut sum: i64 = 0;
        let mut j: usize = i;

        while j < n {
            sum = sum + letter_value(word[j]);
            let len: i64 = (j - i + 1) as i64;

            if sum % len == 0 {
                ans = ans + 1;
            }

            j = j + 1;
        }

        i = i + 1;
    }

    ans
}
