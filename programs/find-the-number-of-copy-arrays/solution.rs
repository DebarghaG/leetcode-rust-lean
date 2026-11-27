pub fn count_arrays(original: &[i64], bounds: &[Vec<i64>]) -> i64 {
    let n = original.len();
    if n == 0 {
        return 0;
    }

    let mut lower: i64 = bounds[0][0] - original[0];
    let mut upper: i64 = bounds[0][1] - original[0];

    let mut i: usize = 1;
    while i < n {
        let lo = bounds[i][0] - original[i];
        let hi = bounds[i][1] - original[i];

        if lo > lower {
            lower = lo;
        }
        if hi < upper {
            upper = hi;
        }

        i = i + 1;
    }

    if upper < lower {
        0
    } else {
        upper - lower + 1
    }
}
