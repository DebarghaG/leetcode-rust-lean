pub fn last_stone_weight(stones: &[i64]) -> i64 {
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < stones.len() {
        v.push(stones[i]);
        i += 1;
    }

    while v.len() > 1 {
        let n: usize = v.len();

        let mut max_i: usize = 0;
        let mut j: usize = 1;
        while j < n {
            if v[j] > v[max_i] {
                max_i = j;
            }
            j += 1;
        }

        let mut second_i: usize = 0;
        if max_i == 0 {
            second_i = 1;
        }

        j = 0;
        while j < n {
            if j != max_i {
                if v[j] > v[second_i] {
                    second_i = j;
                }
            }
            j += 1;
        }

        let y: i64 = v[max_i];
        let x: i64 = v[second_i];

        let mut next: Vec<i64> = Vec::new();
        j = 0;
        while j < n {
            if j != max_i && j != second_i {
                next.push(v[j]);
            }
            j += 1;
        }

        if x != y {
            next.push(y - x);
        }

        v = next;
    }

    if v.len() == 0 {
        0
    } else {
        v[0]
    }
}
