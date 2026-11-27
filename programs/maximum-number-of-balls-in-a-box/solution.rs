fn digit_sum(mut n: i64) -> i64 {
    let mut sum: i64 = 0;
    while n > 0 {
        sum += n % 10;
        n /= 10;
    }
    sum
}

pub fn count_balls(lowLimit: i64, highLimit: i64) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 64 {
        counts.push(0);
        i += 1;
    }

    let mut x: i64 = lowLimit;
    while x <= highLimit {
        let s: i64 = digit_sum(x);
        let idx: usize = s as usize;
        counts[idx] += 1;
        x += 1;
    }

    let mut best: i64 = 0;
    let mut j: usize = 0;
    while j < counts.len() {
        if counts[j] > best {
            best = counts[j];
        }
        j += 1;
    }

    best
}
