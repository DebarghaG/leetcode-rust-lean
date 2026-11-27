pub fn pass_the_pillow(n: i64, time: i64) -> i64 {
    let mut pos: i64 = 1;
    let mut dir: i64 = 1;
    let mut step: i64 = 0;

    while step < time {
        if dir == 1 {
            if pos == n {
                dir = -1;
                pos = pos - 1;
            } else {
                pos = pos + 1;
            }
        } else {
            if pos == 1 {
                dir = 1;
                pos = pos + 1;
            } else {
                pos = pos - 1;
            }
        }
        step = step + 1;
    }

    pos
}
