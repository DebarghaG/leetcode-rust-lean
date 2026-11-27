pub fn execute_instructions(n: i64, startPos: &[i64], s: &[u8]) -> Vec<i64> {
    let m: usize = s.len();
    let mut answer: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < m {
        let mut row: i64 = startPos[0];
        let mut col: i64 = startPos[1];
        let mut count: i64 = 0;
        let mut j: usize = i;

        while j < m {
            let instruction: u8 = s[j];
            let mut next_row: i64 = row;
            let mut next_col: i64 = col;

            if instruction == b'L' {
                next_col = col - 1;
            } else if instruction == b'R' {
                next_col = col + 1;
            } else if instruction == b'U' {
                next_row = row - 1;
            } else {
                next_row = row + 1;
            }

            if next_row < 0 || next_row >= n || next_col < 0 || next_col >= n {
                j = m;
            } else {
                row = next_row;
                col = next_col;
                count += 1;
                j += 1;
            }
        }

        answer.push(count);
        i += 1;
    }

    answer
}
