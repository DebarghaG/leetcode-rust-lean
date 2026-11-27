pub fn num_teams(rating: &[i64]) -> i64 {
    let n = rating.len();
    let mut total: i64 = 0;
    let mut j: usize = 1;

    while j + 1 < n {
        let mut left_less: i64 = 0;
        let mut left_greater: i64 = 0;
        let mut i: usize = 0;

        while i < j {
            if rating[i] < rating[j] {
                left_less += 1;
            } else {
                left_greater += 1;
            }
            i += 1;
        }

        let mut right_less: i64 = 0;
        let mut right_greater: i64 = 0;
        let mut k: usize = j + 1;

        while k < n {
            if rating[k] > rating[j] {
                right_greater += 1;
            } else {
                right_less += 1;
            }
            k += 1;
        }

        total += left_less * right_greater + left_greater * right_less;
        j += 1;
    }

    total
}
