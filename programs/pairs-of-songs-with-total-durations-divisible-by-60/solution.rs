pub fn num_pairs_divisible_by60(time: &[i64]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 60 {
        counts.push(0);
        i += 1;
    }

    let mut total: i64 = 0;
    let mut j: usize = 0;
    while j < time.len() {
        let r: usize = (time[j] % 60) as usize;
        let comp: usize = if r == 0 { 0 } else { 60 - r };

        total += counts[comp];
        counts[r] += 1;

        j += 1;
    }

    total
}
