pub fn punishment_number(n: i64) -> i64 {
    let mut total: i64 = 0;
    let mut i: i64 = 1;

    while i <= n {
        let square: i64 = i * i;

        let mut x: i64 = square;
        let mut rev: Vec<i64> = Vec::new();
        while x > 0 {
            rev.push(x % 10);
            x = x / 10;
        }

        let d: usize = rev.len();
        let mut digits: Vec<i64> = Vec::new();
        let mut j: usize = d;
        while j > 0 {
            j = j - 1;
            digits.push(rev[j]);
        }

        let mut total_masks: usize = 1;
        let mut k: usize = 1;
        while k < d {
            total_masks = total_masks * 2;
            k = k + 1;
        }

        let mut mask: usize = 0;
        let mut ok: bool = false;

        while mask < total_masks {
            let mut sum: i64 = 0;
            let mut cur: i64 = 0;
            let mut place: usize = 1;
            let mut pos: usize = 0;

            while pos < d {
                cur = cur * 10 + digits[pos];

                let mut cut: bool = false;
                if pos + 1 < d {
                    if (mask / place) % 2 == 1 {
                        cut = true;
                    }
                    place = place * 2;
                } else {
                    cut = true;
                }

                if cut {
                    sum = sum + cur;
                    cur = 0;
                }

                pos = pos + 1;
            }

            if sum == i {
                ok = true;
            }

            mask = mask + 1;
        }

        if ok {
            total = total + square;
        }

        i = i + 1;
    }

    total
}
