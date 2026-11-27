pub fn is_robot_bounded(instructions: &[u8]) -> bool {
    let mut x: i64 = 0;
    let mut y: i64 = 0;
    let mut dir: i64 = 0; // 0 = north, 1 = east, 2 = south, 3 = west

    let n = instructions.len();
    let mut i: usize = 0;

    while i < n {
        let c = instructions[i];

        if c == b'G' {
            if dir == 0 {
                y += 1;
            } else if dir == 1 {
                x += 1;
            } else if dir == 2 {
                y -= 1;
            } else {
                x -= 1;
            }
        } else if c == b'L' {
            if dir == 0 {
                dir = 3;
            } else if dir == 1 {
                dir = 0;
            } else if dir == 2 {
                dir = 1;
            } else {
                dir = 2;
            }
        } else if c == b'R' {
            if dir == 0 {
                dir = 1;
            } else if dir == 1 {
                dir = 2;
            } else if dir == 2 {
                dir = 3;
            } else {
                dir = 0;
            }
        }

        i += 1;
    }

    if x == 0 && y == 0 {
        true
    } else {
        dir != 0
    }
}
