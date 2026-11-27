pub fn bag_of_tokens_score(tokens: &[i64], power: i64) -> i64 {
    let n = tokens.len();

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(tokens[i]);
        i += 1;
    }

    // Manual insertion sort in ascending order.
    let mut a: usize = 1;
    while a < n {
        let key = v[a];
        let mut b = a;
        while b > 0 && v[b - 1] > key {
            v[b] = v[b - 1];
            b -= 1;
        }
        v[b] = key;
        a += 1;
    }

    let mut current_power = power;
    let mut score: i64 = 0;
    let mut best: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = n;

    while left < right {
        if current_power >= v[left] {
            current_power -= v[left];
            score += 1;
            left += 1;
            if score > best {
                best = score;
            }
        } else if score >= 1 {
            score -= 1;
            right -= 1;
            current_power += v[right];
        } else {
            break;
        }
    }

    best
}
