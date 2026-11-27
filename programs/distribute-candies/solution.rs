pub fn distribute_candies(candyType: &[i64]) -> i64 {
    let n = candyType.len();
    let mut distinct: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut seen: bool = false;
        let mut j: usize = 0;

        while j < i {
            if candyType[j] == candyType[i] {
                seen = true;
            }
            j += 1;
        }

        if !seen {
            distinct += 1;
        }

        i += 1;
    }

    let half: i64 = (n / 2) as i64;
    if distinct < half {
        distinct
    } else {
        half
    }
}
