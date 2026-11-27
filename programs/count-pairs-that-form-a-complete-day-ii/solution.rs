pub fn count_complete_day_pairs(hours: &[i64]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 24 {
        counts.push(0);
        k += 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < hours.len() {
        let r: i64 = hours[i] % 24;

        let need: i64;
        if r == 0 {
            need = 0;
        } else {
            need = 24 - r;
        }

        ans += counts[need as usize];
        counts[r as usize] += 1;

        i += 1;
    }

    ans
}
