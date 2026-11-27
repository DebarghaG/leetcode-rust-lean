pub fn find_ball(grid: &[Vec<i64>]) -> Vec<i64> {
    let m = grid.len();
    let n = grid[0].len();
    let mut answer: Vec<i64> = Vec::new();

    let mut col: usize = 0;
    while col < n {
        let mut pos: usize = col;
        let mut row: usize = 0;
        let mut stuck: bool = false;

        while row < m {
            let dir = grid[row][pos];

            if dir == 1 {
                if pos + 1 >= n {
                    stuck = true;
                    row = m;
                } else if grid[row][pos + 1] != 1 {
                    stuck = true;
                    row = m;
                } else {
                    pos = pos + 1;
                    row = row + 1;
                }
            } else {
                if pos == 0 {
                    stuck = true;
                    row = m;
                } else if grid[row][pos - 1] != -1 {
                    stuck = true;
                    row = m;
                } else {
                    pos = pos - 1;
                    row = row + 1;
                }
            }
        }

        if stuck {
            answer.push(-1);
        } else {
            answer.push(pos as i64);
        }

        col = col + 1;
    }

    answer
}
