pub fn num_rabbits(answers: &[i64]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 1000 {
        counts.push(0);
        i += 1;
    }

    let n = answers.len();
    let mut j: usize = 0;
    while j < n {
        let a = answers[j] as usize;
        counts[a] = counts[a] + 1;
        j += 1;
    }

    let mut total: i64 = 0;
    let mut k: usize = 0;
    while k < 1000 {
        let cnt = counts[k];
        if cnt > 0 {
            let size = (k as i64) + 1;
            let groups = (cnt + size - 1) / size;
            total = total + groups * size;
        }
        k += 1;
    }

    total
}
