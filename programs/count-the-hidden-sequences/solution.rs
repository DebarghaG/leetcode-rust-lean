pub fn number_of_arrays(differences: &[i64], lower: i64, upper: i64) -> i64 {
    let mut prefix: i64 = 0;
    let mut min_prefix: i64 = 0;
    let mut max_prefix: i64 = 0;

    let mut i: usize = 0;
    while i < differences.len() {
        prefix = prefix + differences[i];
        if prefix < min_prefix {
            min_prefix = prefix;
        }
        if prefix > max_prefix {
            max_prefix = prefix;
        }
        i = i + 1;
    }

    let min_start: i64 = lower - min_prefix;
    let max_start: i64 = upper - max_prefix;

    if max_start < min_start {
        return 0;
    }

    max_start - min_start + 1
}
