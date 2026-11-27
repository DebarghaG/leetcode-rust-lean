pub fn grid_game(grid: &[Vec<i64>]) -> i64 {
    if grid.len() < 2 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut top_suffix: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        top_suffix += grid[0][i];
        i += 1;
    }

    let mut bottom_prefix: i64 = 0;
    let mut ans: i64 = 0;
    i = 0;

    while i < n {
        top_suffix -= grid[0][i];

        let mut second: i64 = top_suffix;
        if bottom_prefix > second {
            second = bottom_prefix;
        }

        if i == 0 {
            ans = second;
        } else {
            if second < ans {
                ans = second;
            }
        }

        bottom_prefix += grid[1][i];
        i += 1;
    }

    ans
}
