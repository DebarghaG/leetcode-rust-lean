pub fn max_score(cardPoints: &[i64], k: i64) -> i64 {
    let n = cardPoints.len();
    let k_usize = k as usize;

    let mut score: i64 = 0;
    let mut i: usize = 0;
    while i < k_usize {
        score += cardPoints[i];
        i += 1;
    }

    let mut best = score;
    let mut take_right: usize = 1;

    while take_right <= k_usize {
        score = score - cardPoints[k_usize - take_right] + cardPoints[n - take_right];
        if score > best {
            best = score;
        }
        take_right += 1;
    }

    best
}
