pub fn largest_combination(candidates: &[i64]) -> i64 {
    let n = candidates.len();
    let mut best: i64 = 0;
    let mut divisor: i64 = 1;
    let mut bit: usize = 0;

    while bit < 63 {
        let mut count: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            let shifted = candidates[i] / divisor;
            if shifted % 2 == 1 {
                count += 1;
            }
            i += 1;
        }

        if count > best {
            best = count;
        }

        if bit < 62 {
            divisor = divisor * 2;
        }
        bit += 1;
    }

    best
}
