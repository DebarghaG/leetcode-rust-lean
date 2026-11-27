pub fn circular_game_losers(n: i64, k: i64) -> Vec<i64> {
    let nn: usize = n as usize;

    let mut seen: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        seen.push(false);
        i += 1;
    }

    seen[0] = true;

    let mut pos: i64 = 0;
    let mut turn: i64 = 1;
    let mut running: bool = true;

    while running {
        let step: i64 = (turn * k) % n;
        let next: i64 = (pos + step) % n;
        let idx: usize = next as usize;

        if seen[idx] {
            running = false;
        } else {
            seen[idx] = true;
            pos = next;
            turn += 1;
        }
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < nn {
        if !seen[j] {
            answer.push((j as i64) + 1);
        }
        j += 1;
    }

    answer
}
