pub fn successful_pairs(spells: &[i64], potions: &[i64], success: i64) -> Vec<i64> {
    let m = potions.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        sorted.push(potions[i]);
        i += 1;
    }

    sorted = merge_sort(sorted);

    let mut result: Vec<i64> = Vec::new();
    let mut s: usize = 0;
    while s < spells.len() {
        let spell = spells[s];

        let mut lo: usize = 0;
        let mut hi: usize = m;

        while lo < hi {
            let mid: usize = lo + (hi - lo) / 2;
            let product = spell * sorted[mid];

            if product >= success {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        result.push((m - lo) as i64);
        s += 1;
    }

    result
}

fn merge_sort(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();

    if n < 2 {
        return v;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        tmp.push(0);
        k += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;

        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if left + width + width < n {
                left + width + width
            } else {
                n
            };

            let mut i = left;
            let mut j = mid;
            let mut t = left;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    tmp[t] = v[i];
                    i += 1;
                } else {
                    tmp[t] = v[j];
                    j += 1;
                }
                t += 1;
            }

            while i < mid {
                tmp[t] = v[i];
                i += 1;
                t += 1;
            }

            while j < right {
                tmp[t] = v[j];
                j += 1;
                t += 1;
            }

            left = right;
        }

        let mut c: usize = 0;
        while c < n {
            v[c] = tmp[c];
            c += 1;
        }

        width = width * 2;
    }

    v
}
