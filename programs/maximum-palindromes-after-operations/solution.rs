pub fn max_palindromes_after_operations(words: &[Vec<u8>]) -> i64 {
    let mut freq: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < 26 {
        freq.push(0);
        z += 1;
    }

    let n = words.len();
    let mut lengths: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let len = words[i].len();
        lengths.push(len as i64);

        let mut j = 0;
        while j < len {
            let c = words[i][j];
            let idx = (c as usize) - 97;
            freq[idx] = freq[idx] + 1;
            j += 1;
        }

        i += 1;
    }

    let mut pairs: i64 = 0;
    let mut f = 0;
    while f < 26 {
        pairs += freq[f] / 2;
        f += 1;
    }

    let total = lengths.len();
    let mut a = 0;
    while a < total {
        let mut b = a + 1;
        while b < total {
            if lengths[b] < lengths[a] {
                let tmp = lengths[a];
                lengths[a] = lengths[b];
                lengths[b] = tmp;
            }
            b += 1;
        }
        a += 1;
    }

    let mut ans: i64 = 0;
    let mut p = 0;
    while p < total {
        let need = lengths[p] / 2;
        if pairs < need {
            break;
        }
        pairs -= need;
        ans += 1;
        p += 1;
    }

    ans
}
