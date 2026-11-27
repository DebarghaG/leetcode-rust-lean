pub fn max_profit(inventory: &[i64], orders: i64) -> i64 {
    let modv: i64 = 1000000007;
    let n: usize = inventory.len();

    if n == 0 {
        return 0;
    }

    let mut maxv: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if inventory[i] > maxv {
            maxv = inventory[i];
        }
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = maxv;

    while lo < hi {
        let mid: i64 = (lo + hi) / 2;
        let mut cnt: i64 = 0;
        let mut j: usize = 0;

        while j < n {
            let a: i64 = inventory[j];
            if a > mid {
                cnt += a - mid;
            }
            j += 1;
        }

        if cnt <= orders {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    let x: i64 = lo;
    let mut total: i64 = 0;
    let mut remaining: i64 = orders;

    let mut k: usize = 0;
    while k < n {
        let a: i64 = inventory[k];
        if a > x {
            let cnt: i64 = a - x;
            let first: i64 = x + 1;
            let s: i64 = (cnt * (first + a)) / 2;

            total = (total + (s % modv)) % modv;
            remaining -= cnt;
        }
        k += 1;
    }

    if remaining > 0 {
        let add: i64 = ((remaining % modv) * (x % modv)) % modv;
        total = (total + add) % modv;
    }

    total
}
