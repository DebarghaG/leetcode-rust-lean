pub fn length_of_longest_substring_two_distinct(s: &[u8]) -> i64 {
    let n = s.len();
    let mut left: usize = 0;
    let mut right: usize = 0;

    let mut char1: u8 = 0;
    let mut char2: u8 = 0;
    let mut count1: i64 = 0;
    let mut count2: i64 = 0;
    let mut distinct: i64 = 0;

    let mut best: i64 = 0;

    while right < n {
        let b: u8 = s[right];

        if distinct == 0 {
            char1 = b;
            count1 = 1;
            distinct = 1;
        } else if b == char1 {
            count1 = count1 + 1;
        } else if distinct == 1 {
            char2 = b;
            count2 = 1;
            distinct = 2;
        } else if b == char2 {
            count2 = count2 + 1;
        } else {
            while count1 > 0 && count2 > 0 {
                let lb: u8 = s[left];
                if lb == char1 {
                    count1 = count1 - 1;
                } else if lb == char2 {
                    count2 = count2 - 1;
                }
                left = left + 1;
            }

            if count1 == 0 {
                char1 = b;
                count1 = 1;
            } else {
                char2 = b;
                count2 = 1;
            }
        }

        let current_len: i64 = (right - left + 1) as i64;
        if current_len > best {
            best = current_len;
        }

        right = right + 1;
    }

    best
}
