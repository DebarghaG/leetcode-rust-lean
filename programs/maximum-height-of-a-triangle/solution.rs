pub fn max_height_of_triangle(red: i64, blue: i64) -> i64 {
    let mut best: i64 = 0;
    let mut scenario: i64 = 0;

    while scenario < 2 {
        let mut r: i64 = red;
        let mut b: i64 = blue;
        let mut height: i64 = 0;
        let mut need_red: bool = scenario == 0;
        let mut size: i64 = 1;

        loop {
            if need_red {
                if r >= size {
                    r = r - size;
                    height = height + 1;
                    need_red = false;
                    size = size + 1;
                } else {
                    break;
                }
            } else {
                if b >= size {
                    b = b - size;
                    height = height + 1;
                    need_red = true;
                    size = size + 1;
                } else {
                    break;
                }
            }
        }

        if height > best {
            best = height;
        }

        scenario = scenario + 1;
    }

    best
}
