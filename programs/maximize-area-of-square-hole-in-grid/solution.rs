pub fn maximize_square_hole_area(n: i64, m: i64, hBars: &[i64], vBars: &[i64]) -> i64 {
    let h = max_consecutive_len(hBars);
    let v = max_consecutive_len(vBars);

    let side = if h < v { h + 1 } else { v + 1 };
    side * side
}

fn max_consecutive_len(bars: &[i64]) -> i64 {
    let len = bars.len();
    if len == 0 {
        return 1;
    }

    let mut best: i64 = 1;
    let mut i: usize = 0;

    while i < len {
        let mut cur: i64 = 1;
        let mut next: i64 = bars[i] + 1;
        let mut searching: bool = true;

        while searching {
            let mut found: bool = false;
            let mut j: usize = 0;

            while j < len {
                if bars[j] == next {
                    found = true;
                }
                j += 1;
            }

            if found {
                cur += 1;
                next += 1;
            } else {
                searching = false;
            }
        }

        if cur > best {
            best = cur;
        }

        i += 1;
    }

    best
}
