fn has_won(board: &[Vec<u8>], p: u8) -> bool {
    let mut won = false;

    let mut i: usize = 0;
    while i < 3 {
        if board[i][0] == p && board[i][1] == p && board[i][2] == p {
            won = true;
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < 3 {
        if board[0][j] == p && board[1][j] == p && board[2][j] == p {
            won = true;
        }
        j += 1;
    }

    if board[0][0] == p && board[1][1] == p && board[2][2] == p {
        won = true;
    }

    if board[0][2] == p && board[1][1] == p && board[2][0] == p {
        won = true;
    }

    won
}

pub fn valid_tic_tac_toe(board: &[Vec<u8>]) -> bool {
    let mut x_count: i64 = 0;
    let mut o_count: i64 = 0;

    let mut i: usize = 0;
    while i < 3 {
        let mut j: usize = 0;
        while j < 3 {
            let cell = board[i][j];
            if cell == b'X' {
                x_count += 1;
            } else if cell == b'O' {
                o_count += 1;
            }
            j += 1;
        }
        i += 1;
    }

    if o_count > x_count || x_count > o_count + 1 {
        return false;
    }

    let x_won = has_won(board, b'X');
    let o_won = has_won(board, b'O');

    if x_won && o_won {
        return false;
    }

    if x_won && x_count != o_count + 1 {
        return false;
    }

    if o_won && x_count != o_count {
        return false;
    }

    true
}
