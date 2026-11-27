pub fn smallest_number(num: i64) -> i64 {
    if num == 0 {
        return 0;
    }

    let is_negative: bool = num < 0;
    let mut x: i64 = num;
    if is_negative {
        x = -x;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut k: i64 = 0;
    while k < 10 {
        counts.push(0);
        k += 1;
    }

    while x > 0 {
        let digit: i64 = x % 10;
        let idx: usize = digit as usize;
        counts[idx] = counts[idx] + 1;
        x = x / 10;
    }

    let mut result: i64 = 0;

    if is_negative {
        let mut d: i64 = 9;
        while d >= 0 {
            let idx: usize = d as usize;
            while counts[idx] > 0 {
                result = result * 10 + d;
                counts[idx] = counts[idx] - 1;
            }
            d -= 1;
        }
        return -result;
    }

    let mut first: i64 = 1;
    while first < 10 {
        let idx: usize = first as usize;
        if counts[idx] > 0 {
            break;
        }
        first += 1;
    }

    if first < 10 {
        let idx: usize = first as usize;
        result = first;
        counts[idx] = counts[idx] - 1;
    }

    let mut d: i64 = 0;
    while d < 10 {
        let idx: usize = d as usize;
        while counts[idx] > 0 {
            result = result * 10 + d;
            counts[idx] = counts[idx] - 1;
        }
        d += 1;
    }

    result
}
