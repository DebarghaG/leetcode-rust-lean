pub fn falling_squares(positions: &[Vec<i64>]) -> Vec<i64> {
    let n = positions.len();

    let mut ans: Vec<i64> = Vec::new();
    let mut lefts: Vec<i64> = Vec::new();
    let mut rights: Vec<i64> = Vec::new();
    let mut tops: Vec<i64> = Vec::new();

    let mut tallest: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let row = &positions[i];
        let left = row[0];
        let side = row[1];
        let right = left + side;

        let mut base: i64 = 0;
        let mut j: usize = 0;

        while j < tops.len() {
            if left < rights[j] && lefts[j] < right {
                if tops[j] > base {
                    base = tops[j];
                }
            }
            j += 1;
        }

        let top = base + side;

        lefts.push(left);
        rights.push(right);
        tops.push(top);

        if top > tallest {
            tallest = top;
        }

        ans.push(tallest);
        i += 1;
    }

    ans
}
