pub fn add_minimum(word: &[u8]) -> i64 {
    let mut ans: i64 = 0;
    let mut expected: i64 = 0; // 0 -> 'a', 1 -> 'b', 2 -> 'c'
    let mut i: usize = 0;

    while i < word.len() {
        let target: i64 = if word[i] == b'a' {
            0
        } else if word[i] == b'b' {
            1
        } else {
            2
        };

        while expected != target {
            ans += 1;
            expected += 1;
            if expected == 3 {
                expected = 0;
            }
        }

        expected += 1;
        if expected == 3 {
            expected = 0;
        }

        i += 1;
    }

    while expected != 0 {
        ans += 1;
        expected += 1;
        if expected == 3 {
            expected = 0;
        }
    }

    ans
}
