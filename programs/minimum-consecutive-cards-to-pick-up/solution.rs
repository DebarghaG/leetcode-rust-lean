pub fn minimum_card_pickup(cards: &[i64]) -> i64 {
    let n = cards.len();
    if n < 2 {
        return -1;
    }

    let mut max_val: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if cards[i] > max_val {
            max_val = cards[i];
        }
        i += 1;
    }

    let size = max_val as usize + 1;
    let mut last: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < size {
        last.push(-1);
        j += 1;
    }

    let mut answer: i64 = n as i64 + 1;
    i = 0;
    while i < n {
        let value = cards[i];
        let index = value as usize;
        let previous = last[index];

        if previous >= 0 {
            let length = i as i64 - previous + 1;
            if length < answer {
                answer = length;
            }
        }

        last[index] = i as i64;
        i += 1;
    }

    if answer == n as i64 + 1 {
        -1
    } else {
        answer
    }
}
