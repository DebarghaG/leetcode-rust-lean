pub fn min_moves(nums: &[i64], limit: i64) -> i64 {
    let n = nums.len();
    let half = n / 2;

    let mut events: Vec<i64> = Vec::new();
    let mut sums: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < half {
        let a = nums[i];
        let b = nums[n - 1 - i];

        sums.push(a + b);

        let mut lo = a;
        let mut hi = b;
        if b < a {
            lo = b;
            hi = a;
        }

        // One replacement can achieve every sum in [lo + 1, hi + limit].
        // Encode interval start as 2*x, and interval removal at right + 1
        // as 2*(right + 1) + 1.
        let left = lo + 1;
        let after_right = hi + limit + 1;

        events.push(2 * left);
        events.push(2 * after_right + 1);

        i += 1;
    }

    events.sort();
    sums.sort();

    let elen = events.len();
    let slen = sums.len();

    let mut best: i64 = 0;
    let mut cur: i64 = 0;
    let mut ei: usize = 0;
    let mut si: usize = 0;

    while ei < elen || si < slen {
        let mut x: i64 = 0;

        if ei < elen {
            x = events[ei] / 2;
        }

        if si < slen {
            let sx = sums[si];
            if ei >= elen || sx < x {
                x = sx;
            }
        }

        while ei < elen && events[ei] / 2 == x {
            let typ = events[ei] % 2;
            if typ == 0 {
                cur += 1;
            } else {
                cur -= 1;
            }
            ei += 1;
        }

        let mut same_sum: i64 = 0;
        while si < slen && sums[si] == x {
            same_sum += 1;
            si += 1;
        }

        let value = cur + same_sum;
        if value > best {
            best = value;
        }
    }

    let total = 2 * (half as i64);
    total - best
}
