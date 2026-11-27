pub fn count_good_rectangles(rectangles: &[Vec<i64>]) -> i64 {
    let n = rectangles.len();
    let mut max_len: i64 = 0;
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let row = &rectangles[i];
        let length = row[0];
        let width = row[1];
        let side = if length < width { length } else { width };

        if side > max_len {
            max_len = side;
            count = 1;
        } else if side == max_len {
            count += 1;
        }

        i += 1;
    }

    count
}
