pub fn deck_revealed_increasing(deck: &[i64]) -> Vec<i64> {
    let n = deck.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(deck[i]);
        i += 1;
    }

    let mut k: usize = 1;
    while k < n {
        let key = sorted[k];
        let mut j = k;
        while j > 0 {
            let prev = sorted[j - 1];
            if prev > key {
                sorted[j] = prev;
                j -= 1;
            } else {
                break;
            }
        }
        sorted[j] = key;
        k += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut a: usize = 0;
    while a < n {
        ans.push(0);
        a += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    let mut qinit: usize = 0;
    while qinit < n {
        queue.push(qinit as i64);
        qinit += 1;
    }

    let mut head: usize = 0;
    let mut val_idx: usize = 0;

    while val_idx < n {
        let pos_i = queue[head];
        head += 1;
        let pos = pos_i as usize;
        ans[pos] = sorted[val_idx];
        val_idx += 1;

        if val_idx < n {
            let moved = queue[head];
            head += 1;
            queue.push(moved);
        }
    }

    ans
}
