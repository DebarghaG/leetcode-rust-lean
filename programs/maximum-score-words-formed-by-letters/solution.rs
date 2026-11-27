pub fn max_score_words(words: &[Vec<u8>], letters: &[Vec<u8>], score: &[i64]) -> i64 {
    let n = words.len();

    let mut avail: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < 26 {
        avail.push(0);
        i += 1;
    }

    i = 0;
    while i < letters.len() {
        let b = letters[i][0];
        let li = (b - b'a') as usize;
        avail[li] = avail[li] + 1;
        i += 1;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut c = 0;
    while c < n * 26 {
        counts.push(0);
        c += 1;
    }

    let mut word_scores: Vec<i64> = Vec::new();
    let mut wi = 0;
    while wi < n {
        word_scores.push(0);
        wi += 1;
    }

    wi = 0;
    while wi < n {
        let w = &words[wi];
        let mut sj = 0;
        while sj < w.len() {
            let b = w[sj];
            let li = (b - b'a') as usize;
            let pos = wi * 26 + li;
            counts[pos] = counts[pos] + 1;
            word_scores[wi] = word_scores[wi] + score[li];
            sj += 1;
        }
        wi += 1;
    }

    let mut total_masks: usize = 1;
    let mut t = 0;
    while t < n {
        total_masks = total_masks * 2;
        t += 1;
    }

    let mut used: Vec<i64> = Vec::new();
    let mut u = 0;
    while u < 26 {
        used.push(0);
        u += 1;
    }

    let mut best: i64 = 0;
    let mut mask: usize = 0;
    while mask < total_masks {
        let mut k = 0;
        while k < 26 {
            used[k] = 0;
            k += 1;
        }

        let mut sum: i64 = 0;
        let mut m = mask;
        let mut j = 0;
        while j < n {
            if m % 2 == 1 {
                let mut q = 0;
                while q < 26 {
                    used[q] = used[q] + counts[j * 26 + q];
                    q += 1;
                }
                sum = sum + word_scores[j];
            }
            m = m / 2;
            j += 1;
        }

        let mut ok = true;
        k = 0;
        while k < 26 {
            if used[k] > avail[k] {
                ok = false;
            }
            k += 1;
        }

        if ok && sum > best {
            best = sum;
        }

        mask = mask + 1;
    }

    best
}
