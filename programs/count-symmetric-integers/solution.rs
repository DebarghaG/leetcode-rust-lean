pub fn count_symmetric_integers(low: i64, high: i64) -> i64 {
    let mut count: i64 = 0;
    let mut x: i64 = low;

    while x <= high {
        let mut d: i64 = 0;
        let mut t: i64 = x;

        while t > 0 {
            d += 1;
            t = t / 10;
        }

        if d % 2 == 0 {
            let n: i64 = d / 2;

            let mut pow: i64 = 1;
            let mut i: i64 = 0;
            while i < n {
                pow = pow * 10;
                i += 1;
            }

            let mut left: i64 = x / pow;
            let mut sum_left: i64 = 0;
            while left > 0 {
                sum_left += left % 10;
                left = left / 10;
            }

            let mut right: i64 = x % pow;
            let mut sum_right: i64 = 0;
            while right > 0 {
                sum_right += right % 10;
                right = right / 10;
            }

            if sum_left == sum_right {
                count += 1;
            }
        }

        x += 1;
    }

    count
}
