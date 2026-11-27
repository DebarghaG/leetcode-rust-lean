fn abs_i64(x: i64) -> i64 {
    if x < 0 {
        -x
    } else {
        x
    }
}

pub fn escape_ghosts(ghosts: &[Vec<i64>], target: &[i64]) -> bool {
    let tx = target[0];
    let ty = target[1];

    let player_dist = abs_i64(tx) + abs_i64(ty);

    let mut i: usize = 0;
    while i < ghosts.len() {
        let gx = ghosts[i][0];
        let gy = ghosts[i][1];

        let ghost_dist = abs_i64(gx - tx) + abs_i64(gy - ty);

        if ghost_dist <= player_dist {
            return false;
        }

        i += 1;
    }

    true
}
