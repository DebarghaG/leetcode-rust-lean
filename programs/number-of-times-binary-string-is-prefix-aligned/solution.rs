pub fn num_times_all_blue(flips: &[i64]) -> i64 {
    let n = flips.len();
    let mut max_flip: i64 = 0;
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let f = flips[i];
        if f > max_flip {
            max_flip = f;
        }

        let step = (i as i64) + 1;
        if max_flip == step {
            count += 1;
        }

        i += 1;
    }

    count
}
