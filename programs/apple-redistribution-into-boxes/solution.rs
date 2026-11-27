pub fn minimum_boxes(apple: &[i64], capacity: &[i64]) -> i64 {
    let mut total_apples: i64 = 0;
    let mut i: usize = 0;
    while i < apple.len() {
        total_apples += apple[i];
        i += 1;
    }

    let n = capacity.len();
    let mut caps: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        caps.push(capacity[j]);
        j += 1;
    }

    // Selection sort in descending order.
    let mut a: usize = 0;
    while a < n {
        let mut max_idx: usize = a;
        let mut b: usize = a + 1;
        while b < n {
            if caps[b] > caps[max_idx] {
                max_idx = b;
            }
            b += 1;
        }

        if max_idx != a {
            let tmp: i64 = caps[a];
            caps[a] = caps[max_idx];
            caps[max_idx] = tmp;
        }

        a += 1;
    }

    let mut used_capacity: i64 = 0;
    let mut boxes: i64 = 0;
    let mut k: usize = 0;
    while k < n {
        if used_capacity >= total_apples {
            return boxes;
        }
        used_capacity += caps[k];
        boxes += 1;
        k += 1;
    }

    boxes
}
