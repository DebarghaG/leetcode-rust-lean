pub fn total_fruit(fruits: &[i64]) -> i64 {
    let n = fruits.len();
    let mut left: usize = 0;
    let mut right: usize = 0;

    let mut type_a: i64 = -1;
    let mut type_b: i64 = -1;
    let mut count_a: i64 = 0;
    let mut count_b: i64 = 0;

    let mut best: i64 = 0;

    while right < n {
        let f = fruits[right];

        if f == type_a {
            count_a += 1;
        } else if f == type_b {
            count_b += 1;
        } else {
            while count_a > 0 && count_b > 0 {
                let g = fruits[left];

                if g == type_a {
                    count_a -= 1;
                } else if g == type_b {
                    count_b -= 1;
                }

                left += 1;
            }

            if count_a == 0 {
                type_a = f;
                count_a = 1;
            } else {
                type_b = f;
                count_b = 1;
            }
        }

        let current_len = count_a + count_b;
        if current_len > best {
            best = current_len;
        }

        right += 1;
    }

    best
}
