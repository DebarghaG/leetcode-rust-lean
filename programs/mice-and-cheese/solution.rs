pub fn mice_and_cheese(reward1: &[i64], reward2: &[i64], k: i64) -> i64 {
    let n = reward1.len();
    let mut total: i64 = 0;
    let mut diffs: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        total += reward2[i];
        diffs.push(reward1[i] - reward2[i]);
        i += 1;
    }

    diffs.sort();

    let kk: usize = k as usize;
    let mut j: usize = 0;
    while j < kk {
        total += diffs[n - 1 - j];
        j += 1;
    }

    total
}
