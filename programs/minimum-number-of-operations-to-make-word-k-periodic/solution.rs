fn block_cmp(word: &[u8], k: usize, a: usize, b: usize) -> i64 {
    let sa = a * k;
    let sb = b * k;
    let mut i: usize = 0;

    while i < k {
        let ca = word[sa + i];
        let cb = word[sb + i];

        if ca < cb {
            return -1;
        }
        if ca > cb {
            return 1;
        }

        i += 1;
    }

    0
}

pub fn minimum_operations_to_make_k_periodic(word: &[u8], k: i64) -> i64 {
    let kk = k as usize;
    let n = word.len();
    let m = n / kk;

    if m <= 1 {
        return 0;
    }

    let mut a: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        a.push(i);
        i += 1;
    }

    let mut b: Vec<usize> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        b.push(0);
        j += 1;
    }

    let mut width: usize = 1;
    while width < m {
        let mut start: usize = 0;

        while start < m {
            let mut mid = start + width;
            if mid > m {
                mid = m;
            }

            let mut end = start + width + width;
            if end > m {
                end = m;
            }

            let mut left = start;
            let mut right = mid;
            let mut out_pos = start;

            while left < mid && right < end {
                if block_cmp(word, kk, a[right], a[left]) < 0 {
                    b[out_pos] = a[right];
                    right += 1;
                } else {
                    b[out_pos] = a[left];
                    left += 1;
                }
                out_pos += 1;
            }

            while left < mid {
                b[out_pos] = a[left];
                left += 1;
                out_pos += 1;
            }

            while right < end {
                b[out_pos] = a[right];
                right += 1;
                out_pos += 1;
            }

            start += width + width;
        }

        let tmp = a;
        a = b;
        b = tmp;

        width += width;
    }

    let mut best: i64 = 0;
    let mut pos: usize = 0;

    while pos < m {
        let mut next = pos + 1;
        let mut same = true;

        while next < m && same {
            if block_cmp(word, kk, a[pos], a[next]) == 0 {
                next += 1;
            } else {
                same = false;
            }
        }

        let cnt = (next - pos) as i64;
        if cnt > best {
            best = cnt;
        }

        pos = next;
    }

    (m as i64) - best
}
