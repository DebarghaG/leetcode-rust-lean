fn ratio_before(a: i64, b: i64, damage: &[i64], turns: &[i64]) -> bool {
    let ai = a as usize;
    let bi = b as usize;
    let lhs = damage[ai] * turns[bi];
    let rhs = damage[bi] * turns[ai];
    if lhs > rhs {
        true
    } else if lhs < rhs {
        false
    } else {
        a < b
    }
}

pub fn min_damage(power: i64, damage: &[i64], health: &[i64]) -> i64 {
    let n = damage.len();

    let mut turns: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let h = health[i];
        let t = (h + power - 1) / power;
        turns.push(t);
        i += 1;
    }

    let mut idx: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        idx.push(i as i64);
        i += 1;
    }

    let mut tmp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + width * 2 < n { start + width * 2 } else { n };

            let mut left = start;
            let mut right = mid;
            let mut out = start;

            while left < mid && right < end {
                let left_id = idx[left];
                let right_id = idx[right];

                if ratio_before(right_id, left_id, damage, &turns) {
                    tmp[out] = right_id;
                    right += 1;
                } else {
                    tmp[out] = left_id;
                    left += 1;
                }
                out += 1;
            }

            while left < mid {
                tmp[out] = idx[left];
                left += 1;
                out += 1;
            }

            while right < end {
                tmp[out] = idx[right];
                right += 1;
                out += 1;
            }

            start += width * 2;
        }

        let mut p = 0usize;
        while p < n {
            idx[p] = tmp[p];
            p += 1;
        }

        width = width * 2;
    }

    let mut total: i64 = 0;
    let mut elapsed: i64 = 0;
    let mut k = 0usize;

    while k < n {
        let id = idx[k] as usize;
        elapsed += turns[id];
        total += elapsed * damage[id];
        k += 1;
    }

    total
}
