pub fn max_number_of_families(n: i64, reservedSeats: &[Vec<i64>]) -> i64 {
    let m = reservedSeats.len();

    let mut keys: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < m {
        let row = reservedSeats[idx][0];
        let seat = reservedSeats[idx][1];
        keys.push(row * 16 + seat);
        idx += 1;
    }

    let mut a: usize = 1;
    while a < m {
        let key = keys[a];
        let mut b: usize = a;
        while b > 0 && keys[b - 1] > key {
            keys[b] = keys[b - 1];
            b -= 1;
        }
        keys[b] = key;
        a += 1;
    }

    let left_mask: i64 = (1i64 << 2) | (1i64 << 3) | (1i64 << 4) | (1i64 << 5);
    let middle_mask: i64 = (1i64 << 4) | (1i64 << 5) | (1i64 << 6) | (1i64 << 7);
    let right_mask: i64 = (1i64 << 6) | (1i64 << 7) | (1i64 << 8) | (1i64 << 9);

    let mut total: i64 = 0;
    let mut rows_used: i64 = 0;
    let mut i: usize = 0;

    while i < m {
        let row = keys[i] / 16;
        let mut mask: i64 = 0;

        while i < m && keys[i] / 16 == row {
            let seat = keys[i] % 16;
            mask = mask | (1i64 << seat);
            i += 1;
        }

        let left_free = (mask & left_mask) == 0;
        let middle_free = (mask & middle_mask) == 0;
        let right_free = (mask & right_mask) == 0;

        if left_free && right_free {
            total += 2;
        } else if left_free || middle_free || right_free {
            total += 1;
        }

        rows_used += 1;
    }

    total + (n - rows_used) * 2
}
