pub fn winning_player_count(n: i64, pick: &[Vec<i64>]) -> i64 {
    let n_usize = n as usize;
    let colors = 11usize;

    let mut counts: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n_usize {
        let mut row: Vec<i64> = Vec::new();
        let mut c = 0usize;
        while c < colors {
            row.push(0);
            c += 1;
        }
        counts.push(row);
        i += 1;
    }

    let mut k = 0usize;
    while k < pick.len() {
        let player = pick[k][0] as usize;
        let color = pick[k][1] as usize;
        counts[player][color] += 1;
        k += 1;
    }

    let mut answer: i64 = 0;
    let mut p = 0usize;
    while p < n_usize {
        let needed: i64 = (p as i64) + 1;
        let mut wins = false;
        let mut c = 0usize;
        while c < colors {
            if counts[p][c] >= needed {
                wins = true;
            }
            c += 1;
        }
        if wins {
            answer += 1;
        }
        p += 1;
    }

    answer
}
