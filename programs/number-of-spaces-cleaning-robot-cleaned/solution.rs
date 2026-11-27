pub fn number_of_clean_rooms(room: &[Vec<i64>]) -> i64 {
    let m = room.len();
    if m == 0 {
        return 0;
    }

    let n = room[0].len();
    if n == 0 {
        return 0;
    }

    let total_cells = m * n;
    let total_states = total_cells * 4;

    let mut seen: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < total_states {
        seen.push(false);
        i = i + 1;
    }

    let mut cleaned: Vec<bool> = Vec::new();
    i = 0;
    while i < total_cells {
        cleaned.push(false);
        i = i + 1;
    }

    let mut r: usize = 0;
    let mut c: usize = 0;
    let mut dir: usize = 0; // 0 = right, 1 = down, 2 = left, 3 = up
    let mut count: i64 = 0;
    let mut step: usize = 0;

    while step < total_states {
        let cell = r * n + c;
        let state = cell * 4 + dir;

        if seen[state] {
            break;
        }
        seen[state] = true;

        if !cleaned[cell] {
            cleaned[cell] = true;
            count = count + 1;
        }

        let mut moved = false;

        if dir == 0 {
            if c + 1 < n && room[r][c + 1] == 0 {
                c = c + 1;
                moved = true;
            }
        } else if dir == 1 {
            if r + 1 < m && room[r + 1][c] == 0 {
                r = r + 1;
                moved = true;
            }
        } else if dir == 2 {
            if c > 0 && room[r][c - 1] == 0 {
                c = c - 1;
                moved = true;
            }
        } else {
            if r > 0 && room[r - 1][c] == 0 {
                r = r - 1;
                moved = true;
            }
        }

        if !moved {
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

        step = step + 1;
    }

    count
}
