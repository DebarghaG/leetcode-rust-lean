pub fn count_stepping_numbers(low: i64, high: i64) -> Vec<i64> {
    let mut all: Vec<i64> = Vec::new();

    // 0 is a stepping number and must not be expanded, since that could
    // create leading-zero duplicates.
    all.push(0);

    // All one-digit positive numbers are stepping numbers.
    let mut d: i64 = 1;
    while d <= 9 {
        if d <= high {
            all.push(d);
        }
        d += 1;
    }

    // Generate all stepping numbers <= high using a queue-like Vec.
    let mut idx: usize = 0;
    while idx < all.len() {
        let x = all[idx];

        if x > 0 {
            let last = x % 10;

            if last > 0 {
                let next = x * 10 + (last - 1);
                if next <= high {
                    all.push(next);
                }
            }

            if last < 9 {
                let next = x * 10 + (last + 1);
                if next <= high {
                    all.push(next);
                }
            }
        }

        idx += 1;
    }

    // Keep only values in [low, high].
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < all.len() {
        if all[i] >= low {
            result.push(all[i]);
        }
        i += 1;
    }

    // Insertion sort in ascending order.
    let mut i2: usize = 1;
    while i2 < result.len() {
        let key = result[i2];
        let mut j: usize = i2;

        while j > 0 {
            if result[j - 1] <= key {
                break;
            }
            result[j] = result[j - 1];
            j -= 1;
        }

        result[j] = key;
        i2 += 1;
    }

    result
}
