pub fn minimum_keypresses(s: &[u8]) -> i64 {
    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        freq.push(0);
        i += 1;
    }

    let mut index: usize = 0;
    while index < s.len() {
        let letter: usize = (s[index] - b'a') as usize;
        freq[letter] = freq[letter] + 1;
        index += 1;
    }

    let mut i: usize = 0;
    while i < 26 {
        let mut j: usize = i + 1;
        while j < 26 {
            if freq[j] > freq[i] {
                let temp: i64 = freq[i];
                freq[i] = freq[j];
                freq[j] = temp;
            }
            j += 1;
        }
        i += 1;
    }

    let mut answer: i64 = 0;
    let mut i: usize = 0;
    while i < 26 {
        let cost: i64;
        if i < 9 {
            cost = 1;
        } else if i < 18 {
            cost = 2;
        } else {
            cost = 3;
        }
        answer = answer + freq[i] * cost;
        i += 1;
    }

    answer
}
