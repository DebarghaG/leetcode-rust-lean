pub fn count_largest_group(n: i64) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 50 {
        counts.push(0);
        k += 1;
    }

    let mut num: i64 = 1;
    while num <= n {
        let mut x: i64 = num;
        let mut digit_sum: i64 = 0;
        while x > 0 {
            digit_sum += x % 10;
            x = x / 10;
        }

        let idx: usize = digit_sum as usize;
        counts[idx] = counts[idx] + 1;
        num += 1;
    }

    let mut best: i64 = 0;
    let mut i: usize = 0;
    while i < 50 {
        if counts[i] > best {
            best = counts[i];
        }
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut j: usize = 0;
    while j < 50 {
        if counts[j] == best {
            ans += 1;
        }
        j += 1;
    }

    ans
}
