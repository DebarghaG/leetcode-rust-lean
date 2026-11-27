fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

pub fn has_groups_size_x(deck: &[i64]) -> bool {
    let n = deck.len();
    if n == 0 {
        return false;
    }

    let mut max_val = deck[0];
    let mut i = 0;
    while i < n {
        if deck[i] > max_val {
            max_val = deck[i];
        }
        i += 1;
    }

    let m = (max_val + 1) as usize;

    let mut counts: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < m {
        counts.push(0);
        j += 1;
    }

    let mut k = 0;
    while k < n {
        let value = deck[k] as usize;
        counts[value] = counts[value] + 1;
        k += 1;
    }

    let mut g = 0;
    let mut idx = 0;
    while idx < m {
        let c = counts[idx];
        if c > 0 {
            if g == 0 {
                g = c;
            } else {
                g = gcd(g, c);
            }
        }
        idx += 1;
    }

    g > 1
}
