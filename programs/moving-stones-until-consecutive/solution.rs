pub fn num_moves_stones(a: i64, b: i64, c: i64) -> Vec<i64> {
    let mut x = a;
    let mut y = b;
    let mut z = c;
    let mut t: i64 = 0;

    if x > y {
        t = x;
        x = y;
        y = t;
    }
    if y > z {
        t = y;
        y = z;
        z = t;
    }
    if x > y {
        t = x;
        x = y;
        y = t;
    }

    let mut min_moves: i64 = 2;
    if z - x == 2 {
        min_moves = 0;
    } else if y - x <= 2 || z - y <= 2 {
        min_moves = 1;
    }

    let max_moves: i64 = z - x - 2;

    let mut ans: Vec<i64> = Vec::new();
    ans.push(min_moves);
    ans.push(max_moves);
    ans
}
