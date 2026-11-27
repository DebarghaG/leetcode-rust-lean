pub fn final_position_of_snake(n: i64, commands: &[Vec<u8>]) -> i64 {
    let mut row: i64 = 0;
    let mut col: i64 = 0;

    let mut i: usize = 0;
    while i < commands.len() {
        let cmd = &commands[i];
        if cmd.len() > 0 {
            let c = cmd[0];
            if c == b'U' {
                row -= 1;
            } else if c == b'D' {
                row += 1;
            } else if c == b'L' {
                col -= 1;
            } else if c == b'R' {
                col += 1;
            }
        }
        i += 1;
    }

    row * n + col
}
